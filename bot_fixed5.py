"""
NexAuth — Telegram TOTP Authenticator Bot  (v5 — Full Rewrite & Bug-Fixed)
===========================================================================

BUG FIXES (v4 → v5)
────────────────────
• [FIX] UPD_OK callback: callback_data now carries a short numeric cache-key
        instead of the raw svc name, so it never exceeds Telegram's 64-byte
        callback_data limit for accounts with long names (e.g. email addresses).
• [FIX] Double q.answer() crash: rate-limiter no longer calls q.answer() a
        second time after it was already answered — uses q.message.reply_text
        with show_alert instead.
• [FIX] _resolve() collision: DEL_OK / UPD_OK used raw svc name in
        callback_data; if svc happened to be all-digits, _resolve() would
        misinterpret it as a cache index. Each prefix now uses its own resolver.
• [FIX] Stale _acct_cache after rename/delete: cache is now invalidated on
        every mutating operation (add, delete, rename, update).
• [FIX] pyotp algorithm mapping: SHA256 and SHA512 now correctly map to
        pyotp's hashlib digest parameter instead of silently falling back.
• [FIX] on_photo session check: auto-session for no-PIN users was missing in
        the photo handler — new users sending a QR got "Vault Locked".
• [FIX] _save_and_show duplicate-update: pending_update stored per-uid in a
        server-side dict (not ctx.user_data) so it survives across the callback
        boundary without being cleared by other handlers.
• [FIX] Export URI URL-encoding: issuer and account in otpauth URI are now
        percent-encoded so special characters (@ + space) roundtrip correctly.
• [FIX] Rename DB uniqueness: db_rename now catches DuplicateKeyError and
        returns False with a clear error message instead of silently failing.
• [FIX] Stats query N+1: algorithm breakdown no longer fires one DB query per
        account — uses a single aggregation pipeline.

NEW FEATURES (v5)
────────────────────
• 🔔 Notification / OTP copy button: inline "📋 Copy OTP" button sends the
      raw digits as a separate message the user can tap-to-copy.
• 🔐 HOTP support: accounts with counter-based HOTP are detected from URI and
      stored with type="hotp"; Get OTP increments the counter atomically.
• 🌍 Multi-account QR: if a QR image contains multiple otpauth URIs (rare but
      real), all are offered to the user via an inline picker.
• 🕵 Audit log: every vault action (add/delete/rename/unlock/export) is
      appended to a capped MongoDB collection for admin review.
• 🔢 Custom digits/period on manual entry: after entering a base32 key the bot
      now asks for digits (6/8) and period (30/60) before saving.
• 📌 Favourite accounts: star ⭐ an account; starred accounts sort to the top
      of all lists.
• 🔒 Paranoid mode: opt-in setting that deletes OTP messages after 60 s.
• 🗓 Monthly digest: /digest prints a per-month add/delete activity summary.
• 📊 Admin /stats command shows total users, total accounts, error rate.
• 🔄 Atomic counter for HOTP — no double-increment under concurrent requests.
• 🗄 MongoDB storage panel: /admin_stats and Bot Health now show data size,
      allocated storage, index size, and free space (Atlas freeStorageSize
      or filesystem level on self-hosted), with a visual usage bar.
"""

from __future__ import annotations

import asyncio
import base64
import hashlib
import hmac
import io
import json
import logging
import os
import re
import time
from collections import defaultdict
from urllib.parse import quote, unquote
from datetime import datetime, timezone, timedelta
from typing import Optional

import pyotp
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from dotenv import load_dotenv
import zxingcpp
from PIL import Image
from pymongo import MongoClient, ASCENDING
from pymongo.errors import DuplicateKeyError, BulkWriteError
from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    ReplyKeyboardMarkup,
)
from telegram.constants import ParseMode, ChatAction
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ─────────────────────────────────────────────────────────────
# 1.  ENV & LOGGING
# ─────────────────────────────────────────────────────────────
load_dotenv()

logging.basicConfig(
    format="%(asctime)s  %(levelname)-8s  %(name)s  %(message)s",
    level=logging.INFO,
)
log = logging.getLogger("NexAuth")

BOT_TOKEN      = os.environ["BOT_TOKEN"]
MONGO_URI      = os.environ["MONGO_URI"]
ENCRYPTION_KEY = os.environ["ENCRYPTION_KEY"]
SESSION_TTL    = int(os.getenv("SESSION_TIMEOUT", "120"))
PAGE_SIZE      = 8
PIN_LOCKOUT_S  = 300    # 5-min lockout after 5 wrong PINs
EXPORT_TTL_S   = 30     # seconds before export URI message is deleted
BACKUP_TTL_S   = 15     # seconds before backup token message is deleted
PARANOID_TTL_S = 60     # seconds before OTP message deleted in paranoid mode

# ADMIN_ID is required — must be a real Telegram user ID, never 0
_admin_id_raw = os.getenv("ADMIN_ID", "").strip()
if not _admin_id_raw or not _admin_id_raw.lstrip("-").isdigit():
    raise RuntimeError(
        "ADMIN_ID is not set or invalid in your .env file.\n"
        "Add:  ADMIN_ID=123456789   (your Telegram numeric user ID)"
    )
ADMIN_ID = int(_admin_id_raw)

# ─────────────────────────────────────────────────────────────
# 2.  AES-256-GCM  &  PIN HASHING
# ─────────────────────────────────────────────────────────────
def _build_key(raw: str) -> bytes:
    for decoder in (bytes.fromhex, base64.b64decode):
        try:
            k = decoder(raw)
            if len(k) == 32:
                return k
        except Exception:
            pass
    return hashlib.sha256(raw.encode()).digest()


_AESKEY = _build_key(ENCRYPTION_KEY)


def aes_encrypt(plaintext: str) -> str:
    nonce = os.urandom(12)
    ct    = AESGCM(_AESKEY).encrypt(nonce, plaintext.encode(), None)
    return base64.urlsafe_b64encode(nonce + ct).decode()


def aes_decrypt(token: str) -> str:
    raw       = base64.urlsafe_b64decode(token)
    nonce, ct = raw[:12], raw[12:]
    return AESGCM(_AESKEY).decrypt(nonce, ct, None).decode()


def hash_pin(pin: str) -> str:
    return hashlib.pbkdf2_hmac(
        "sha256", pin.encode(), _AESKEY[:16], 100_000
    ).hex()


def verify_pin(pin: str, stored_hash: str) -> bool:
    return hmac.compare_digest(hash_pin(pin), stored_hash)


# ─────────────────────────────────────────────────────────────
# 3.  MONGODB
# ─────────────────────────────────────────────────────────────
_client      = MongoClient(MONGO_URI, serverSelectionTimeoutMS=6_000)
_db          = _client["nexauth"]
col_users         = _db["users"]
col_accounts      = _db["otp_accounts"]
col_sessions      = _db["sessions"]
col_audit         = _db["audit_log"]
col_reset_requests = _db["reset_requests"]


def _setup_indexes() -> None:
    """
    Drop every non-default index on each collection, then recreate exactly
    the ones we want.  This guarantees no stale unique indexes from old schema
    versions survive across restarts — which was the root cause of the
    'already exists' false-positive on every insert.
    """
    def _drop_all_custom(col):
        existing = col.index_information()
        for idx_name, idx_info in list(existing.items()):
            if idx_name == "_id_":          # never drop the default _id index
                continue
            try:
                col.drop_index(idx_name)
                log.info("Dropped old index '%s' from '%s'", idx_name, col.name)
            except Exception as e:
                log.warning("Could not drop index '%s' from '%s': %s", idx_name, col.name, e)

    _drop_all_custom(col_users)
    _drop_all_custom(col_accounts)
    _drop_all_custom(col_sessions)

    # Recreate exactly what we need — nothing more
    col_users.create_index("uid", unique=True)
    col_accounts.create_index([("uid", ASCENDING), ("svc", ASCENDING)], unique=True)
    col_sessions.create_index("uid", unique=True)
    col_audit.create_index("ts", expireAfterSeconds=90 * 86400)
    col_reset_requests.create_index("uid")
    col_reset_requests.create_index("ts", expireAfterSeconds=7 * 86400)
    log.info("MongoDB indexes verified.")


_setup_indexes()


def db_upsert_user(uid: int, name: str, username: Optional[str]) -> None:
    now = datetime.now(timezone.utc)
    try:
        col_users.update_one(
            {"uid": uid},
            {
                "$setOnInsert": {"uid": uid, "username": username, "joined": now},
                "$set": {"last_seen": now, "name": name},
            },
            upsert=True,
        )
    except DuplicateKeyError:
        col_users.update_one(
            {"uid": uid},
            {"$set": {"last_seen": now, "name": name}},
        )
    except Exception as e:
        log.error("db_upsert_user uid=%s error: %s", uid, e)


def db_get(uid: int, svc: str) -> Optional[dict]:
    return col_accounts.find_one({"uid": uid, "svc": svc})


def db_list(uid: int) -> list:
    return list(col_accounts.find(
        {"uid": uid},
        {"svc": 1, "issuer": 1, "created": 1, "digits": 1, "period": 1,
         "algorithm": 1, "type": 1, "starred": 1, "_id": 0},
    ))


def db_add(uid: int, svc: str, issuer: str, enc_secret: str,
           digits: int = 6, period: int = 30, algorithm: str = "SHA1",
           otp_type: str = "totp", counter: int = 0) -> bool:
    """
    Returns True if a NEW document was inserted.
    Returns False if (uid, svc) already exists.

    FIX: explicitly checks existence BEFORE insert so the caller gets a
    reliable True/False regardless of which indexes are active in MongoDB.
    The DuplicateKeyError catch is kept as a safety net.
    """
    # Explicit pre-check — definitive, index-independent
    if col_accounts.find_one({"uid": uid, "svc": svc}, {"_id": 1}):
        _invalidate_cache(uid)
        return False

    try:
        col_accounts.insert_one({
            "uid":       uid,
            "svc":       svc,
            "issuer":    issuer,
            "enc":       enc_secret,
            "digits":    digits,
            "period":    period,
            "algorithm": algorithm,
            "type":      otp_type,
            "counter":   counter,
            "starred":   False,
            "created":   datetime.now(timezone.utc),
        })
        _invalidate_cache(uid)
        return True
    except DuplicateKeyError:
        _invalidate_cache(uid)
        return False


def db_update_secret(uid: int, svc: str, enc_secret: str, issuer: str,
                     digits: int, period: int, algorithm: str) -> None:
    col_accounts.update_one(
        {"uid": uid, "svc": svc},
        {"$set": {
            "enc": enc_secret, "issuer": issuer,
            "digits": digits, "period": period, "algorithm": algorithm,
            "updated": datetime.now(timezone.utc),
        }},
    )
    _invalidate_cache(uid)


def db_delete(uid: int, svc: str) -> bool:
    ok = col_accounts.delete_one({"uid": uid, "svc": svc}).deleted_count > 0
    if ok:
        _invalidate_cache(uid)
    return ok


def db_rename(uid: int, old: str, new: str) -> bool:
    """Returns True on success, False on failure or name collision."""
    try:
        result = col_accounts.update_one(
            {"uid": uid, "svc": old},
            {"$set": {"svc": new}},
        )
        if result.modified_count:
            _invalidate_cache(uid)
            return True
        return False
    except DuplicateKeyError:
        return False
    except Exception as e:
        log.error("db_rename uid=%s %s->%s error: %s", uid, old, new, e)
        return False


def db_toggle_star(uid: int, svc: str) -> bool:
    doc = col_accounts.find_one({"uid": uid, "svc": svc}, {"starred": 1})
    if not doc:
        return False
    col_accounts.update_one(
        {"uid": uid, "svc": svc},
        {"$set": {"starred": not doc.get("starred", False)}},
    )
    _invalidate_cache(uid)
    return True


def db_search(uid: int, query: str) -> list:
    regex = re.compile(re.escape(query), re.IGNORECASE)
    return list(col_accounts.find(
        {"uid": uid, "$or": [{"svc": regex}, {"issuer": regex}]},
        {"svc": 1, "issuer": 1, "created": 1, "starred": 1, "_id": 0},
    ))


def db_get_pin(uid: int) -> Optional[str]:
    doc = col_users.find_one({"uid": uid}, {"pin_hash": 1})
    return (doc or {}).get("pin_hash")


def db_set_pin(uid: int, pin_hash: Optional[str]) -> None:
    col_users.update_one({"uid": uid}, {"$set": {"pin_hash": pin_hash}})


def db_record_unlock(uid: int) -> None:
    col_users.update_one({"uid": uid}, {"$set": {"last_unlock": datetime.now(timezone.utc)}})


def db_get_setting(uid: int, key: str, default=None):
    doc = col_users.find_one({"uid": uid}, {key: 1})
    return (doc or {}).get(key, default)


def db_set_setting(uid: int, key: str, value) -> None:
    col_users.update_one({"uid": uid}, {"$set": {key: value}})


def db_hotp_increment(uid: int, svc: str) -> int:
    """Atomically increment HOTP counter and return the NEW counter value."""
    doc = col_accounts.find_one_and_update(
        {"uid": uid, "svc": svc},
        {"$inc": {"counter": 1}},
        return_document=True,
        projection={"counter": 1},
    )
    return doc["counter"] if doc else 0


def audit(uid: int, action: str, detail: str = "") -> None:
    try:
        col_audit.insert_one({
            "uid": uid, "action": action, "detail": detail,
            "ts": datetime.now(timezone.utc),
        })
    except Exception:
        pass


# ── Passcode Reset DB helpers ────────────────────────────────
def db_get_reset_request(request_id: str) -> Optional[dict]:
    return col_reset_requests.find_one({"request_id": request_id})


def db_get_reset_request_by_uid(uid: int) -> Optional[dict]:
    return col_reset_requests.find_one({"uid": uid, "status": "pending"})


def db_update_reset_status(request_id: str, status: str) -> None:
    col_reset_requests.update_one(
        {"request_id": request_id},
        {"$set": {"status": status, "updated": datetime.now(timezone.utc)}},
    )


def db_delete_reset_request(request_id: str) -> None:
    col_reset_requests.delete_one({"request_id": request_id})


def db_create_reset_request_with_qa(uid: int, name: str, username,
                                     qa_plain: list) -> str:
    """Create a reset request that includes plaintext Q&A for admin review."""
    request_id = base64.urlsafe_b64encode(os.urandom(9)).decode().rstrip("=")
    col_reset_requests.insert_one({
        "request_id": request_id,
        "uid": uid,
        "name": name,
        "username": username,
        "status": "pending",
        "qa": qa_plain,
        "ts": datetime.now(timezone.utc),
    })
    return request_id


# ── Security Questions DB helpers ────────────────────────────
SECURITY_QUESTIONS = [
    "What is your recovery email address?",
    "What is the name of the city where you were born?",
]



def db_save_security_answers(uid: int, answers: list) -> None:
    col_users.update_one(
        {"uid": uid},
        {"$set": {
            # Store encrypted plaintext so admin can compare during appeals
            "security_answers_enc": [aes_encrypt(a.strip()) for a in answers],
        }},
    )


def db_get_security_answers_plain(uid: int):
    """Return list of decrypted plaintext answers, or None if not set."""
    doc = col_users.find_one({"uid": uid}, {"security_answers_enc": 1})
    enc_list = (doc or {}).get("security_answers_enc")
    if not enc_list:
        return None
    try:
        return [aes_decrypt(e) for e in enc_list]
    except Exception:
        return None


def db_get_security_answers(uid: int):
    doc = col_users.find_one({"uid": uid}, {"security_answers_enc": 1})
    return (doc or {}).get("security_answers_enc")


def db_has_security_answers(uid: int) -> bool:
    ans = db_get_security_answers(uid)
    return bool(ans and len(ans) >= 1)



# ─────────────────────────────────────────────────────────────
# 4.  SESSION
# ─────────────────────────────────────────────────────────────

# In-memory cache: uid → datetime (UTC) of last touch.
# Using wall-clock datetime (not monotonic) so the cache stays
# correct across process restarts and bot_data reloads.
_session_cache: dict[int, datetime] = {}

# Per-user auto-lock tasks: uid → asyncio.Task
# Each task sleeps for SESSION_TTL then fires the lock notification.
# Replaced every time session_touch() is called.
_auto_lock_tasks: dict[int, "asyncio.Task[None]"] = {}

# Tracks active admin-reminder tasks for reset requests: request_id → asyncio.Task
_reset_reminder_tasks: dict[str, asyncio.Task] = {}

# Tracks the current admin notification message_id for each request: request_id → int
_reset_admin_msg_ids: dict[str, int] = {}

# Forward reference — filled in main() after the Application is built
_bot_ref = None


def session_touch(uid: int) -> None:
    """Record activity for uid. Resets the inactivity timer."""
    now = datetime.now(timezone.utc)
    _session_cache[uid] = now
    col_sessions.update_one(
        {"uid": uid},
        {"$set": {"last": now}},
        upsert=True,
    )
    # Reschedule per-user auto-lock: cancel old task, spawn fresh one
    old = _auto_lock_tasks.pop(uid, None)
    if old and not old.done():
        old.cancel()
    task = asyncio.ensure_future(_auto_lock_user(uid))
    _auto_lock_tasks[uid] = task


async def _auto_lock_user(uid: int) -> None:
    """Sleep for SESSION_TTL then lock the user and send a notification."""
    if uid == ADMIN_ID:
        return  # Admin is never auto-locked
    try:
        await asyncio.sleep(SESSION_TTL)
    except asyncio.CancelledError:
        return  # session_touch() rescheduled us — do nothing

    # Confirm session is truly expired (clock check, not cache)
    doc = col_sessions.find_one({"uid": uid})
    if doc:
        last = doc["last"]
        if last.tzinfo is None:
            last = last.replace(tzinfo=timezone.utc)
        elapsed = (datetime.now(timezone.utc) - last).total_seconds()
        if elapsed < SESSION_TTL:
            # A concurrent touch happened — bail out, the new task will handle it
            return

    # Kill the session
    _session_cache.pop(uid, None)
    _auto_lock_tasks.pop(uid, None)
    col_sessions.delete_one({"uid": uid})

    # Only notify if the user actually has a PIN (no-PIN users have no lock screen)
    pin_hash = db_get_pin(uid)
    if not pin_hash:
        return

    bot = _bot_ref
    if bot is None:
        return
    try:
        await bot.send_message(
            chat_id=uid,
            text=(
                "🔒 *Vault Auto-Locked*\n\n"
                f"Your session expired after *{SESSION_TTL // 60} min* of inactivity.\n\n"
                "🛡 *Your OTP secrets are protected.*\n"
                "Tap *🔓 Unlock Vault* and enter your passcode to continue."
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )
        log.info("Auto-lock: sent lock notification to uid=%s", uid)
    except TelegramError as te:
        log.warning("Auto-lock: could not notify uid=%s — %s", uid, te)


def session_alive(uid: int) -> bool:
    """Return True if uid has an unexpired session."""
    # 1. Fast in-memory check (datetime-based, survives restarts correctly)
    cached = _session_cache.get(uid)
    if cached is not None:
        if (datetime.now(timezone.utc) - cached).total_seconds() < SESSION_TTL:
            return True
        else:
            # Cache says expired — evict and fall through to DB check
            _session_cache.pop(uid, None)

    # 2. DB check (authoritative)
    doc = col_sessions.find_one({"uid": uid})
    if not doc:
        return False
    last = doc["last"]
    if last.tzinfo is None:
        last = last.replace(tzinfo=timezone.utc)
    alive = (datetime.now(timezone.utc) - last).total_seconds() < SESSION_TTL
    if alive:
        _session_cache[uid] = last   # warm the cache from DB
    else:
        col_sessions.delete_one({"uid": uid})  # clean up stale row
    return alive


def session_kill(uid: int) -> None:
    """Immediately kill uid's session (manual lock, PIN change, etc.)."""
    _session_cache.pop(uid, None)
    col_sessions.delete_one({"uid": uid})
    task = _auto_lock_tasks.pop(uid, None)
    if task and not task.done():
        task.cancel()


# ─────────────────────────────────────────────────────────────
# 5.  RATE LIMITER
# ─────────────────────────────────────────────────────────────
_hits: dict = defaultdict(list)
RATE_WIN, RATE_MAX = 60, 30


def rate_ok(uid: int) -> bool:
    now  = time.monotonic()
    prev = [t for t in _hits[uid] if now - t < RATE_WIN]
    if len(prev) >= RATE_MAX:
        return False
    prev.append(now)
    _hits[uid] = prev
    return True


# ─────────────────────────────────────────────────────────────
# 6.  SECRET / URI PARSING
# ─────────────────────────────────────────────────────────────
_URI_RE  = re.compile(r"otpauth://(totp|hotp)/([^?]+)\?([^#\s]+)", re.I)
_B32_RE  = re.compile(r"^[A-Z2-7]{16,512}=*$")
_SVC_RE  = re.compile(r"^[A-Za-z0-9 ._\-@]{1,64}$")
_PIN_RE  = re.compile(r"^\d{4,8}$")

# pyotp digest map for non-SHA1 algorithms
import hashlib as _hashlib
_ALGO_MAP = {
    "SHA1":   _hashlib.sha1,
    "SHA256": _hashlib.sha256,
    "SHA512": _hashlib.sha512,
}


def _make_totp(secret: str, digits: int, period: int, algorithm: str) -> pyotp.TOTP:
    digest = _ALGO_MAP.get(algorithm.upper(), _hashlib.sha1)
    return pyotp.TOTP(secret, digits=digits, interval=period, digest=digest)


def _make_hotp(secret: str, digits: int, counter: int, algorithm: str) -> pyotp.HOTP:
    digest = _ALGO_MAP.get(algorithm.upper(), _hashlib.sha1)
    return pyotp.HOTP(secret, digits=digits, digest=digest, initial_count=counter)


def parse_otpauth(uri: str) -> Optional[dict]:
    m = _URI_RE.search(uri)
    if not m:
        return None
    otp_type = m.group(1).lower()
    label    = unquote(m.group(2)).strip()
    params   = {
        k: unquote(v)
        for k, v in (
            p.split("=", 1) for p in m.group(3).split("&") if "=" in p
        )
    }
    secret = params.get("secret", "").upper().replace(" ", "").replace("-", "")
    if not _B32_RE.match(secret):
        return None

    # Split "issuer:account" label — colon is the standard separator
    if ":" in label:
        issuer_label, account = label.split(":", 1)
        issuer_label = issuer_label.strip()
        account      = account.strip()
    else:
        issuer_label = ""
        account      = label.strip()

    # Canonical issuer: prefer the ?issuer= param, fall back to label prefix
    issuer = params.get("issuer", issuer_label or account).strip()

    # svc: prefer the account portion of the label; fall back to issuer param
    # Collapse whitespace but do NOT strip the account vs issuer distinction —
    # this is the key fix: two different accounts at the same issuer
    # (e.g. "Google:alice@example.com" vs "Google:bob@example.com")
    # must NOT share the same svc key.
    svc = " ".join((account or issuer).split())[:64]

    return {
        "svc":       svc,
        "issuer":    issuer[:64],
        "secret":    secret,
        "digits":    int(params.get("digits", 6)),
        "period":    int(params.get("period", 30)),
        "algorithm": params.get("algorithm", "SHA1").upper(),
        "type":      otp_type,
        "counter":   int(params.get("counter", 0)),
    }


def parse_b32(text: str) -> Optional[str]:
    candidate = text.upper().replace(" ", "").replace("-", "")
    return candidate if _B32_RE.match(candidate) else None


def decode_qr_image(image_bytes: bytes) -> list[str]:
    """Return list of all otpauth URIs found in image (may be multiple)."""
    uris = []
    try:
        img     = Image.open(io.BytesIO(image_bytes)).convert("RGB")
        results = zxingcpp.read_barcodes(img)
        for r in results:
            if r.text.lower().startswith("otpauth://"):
                uris.append(r.text)
    except Exception as e:
        log.warning("QR decode error: %s", e)
    return uris


# ─────────────────────────────────────────────────────────────
# 7.  SPINNER ANIMATION
# ─────────────────────────────────────────────────────────────
_SPIN = ("⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏")


async def spin(msg, label: str, rounds: int = 6) -> None:
    for i in range(rounds):
        try:
            await msg.edit_text(
                f"`{_SPIN[i % len(_SPIN)]}` _{label}_",
                parse_mode=ParseMode.MARKDOWN,
            )
        except (BadRequest, TelegramError):
            pass
        await asyncio.sleep(0.15)


# ─────────────────────────────────────────────────────────────
# 8.  REPLY KEYBOARDS
# ─────────────────────────────────────────────────────────────
def rkb_home() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("➕ Add Account"),  KeyboardButton("🔑 Get OTP")],
            [KeyboardButton("📋 My Accounts"),  KeyboardButton("🔍 Search")],
            [KeyboardButton("🔒 Lock Vault"),   KeyboardButton("⚙️ Settings")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_add_menu() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("📷 Scan QR Code")],
            [KeyboardButton("🔗 Paste URI"), KeyboardButton("🔐 Enter Secret Key")],
            [KeyboardButton("🔙 Back")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_settings() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("🗑 Delete Account"), KeyboardButton("✏️ Rename")],
            [KeyboardButton("💾 Backup"),          KeyboardButton("📥 Restore")],
            [KeyboardButton("🔑 Set Passcode"),    KeyboardButton("🔓 Remove Passcode")],
            [KeyboardButton("🔕 Paranoid Mode"),   KeyboardButton("🕐 Session Info")],
            [KeyboardButton("📊 My Stats"),        KeyboardButton("❓ Help")],
            [KeyboardButton("🔙 Back")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_back() -> ReplyKeyboardMarkup:
    """Single back button. Replaces the identical rkb_back_home / rkb_back_settings / rkb_back_add."""
    return ReplyKeyboardMarkup(
        [[KeyboardButton("🔙 Back")]],
        resize_keyboard=True,
        is_persistent=True,
    )


# Aliases kept for call-site compatibility
rkb_back_home     = rkb_back
rkb_back_settings = rkb_back
rkb_back_add      = rkb_back


def rkb_cancel() -> ReplyKeyboardMarkup:
    """❌ Cancel + 🔙 Back — used in input-wait states from Home."""
    return ReplyKeyboardMarkup(
        [[KeyboardButton("❌ Cancel"), KeyboardButton("🔙 Back")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_cancel_settings() -> ReplyKeyboardMarkup:
    """❌ Cancel + 🔙 Back — used in input-wait states from Settings."""
    return ReplyKeyboardMarkup(
        [[KeyboardButton("❌ Cancel"), KeyboardButton("🔙 Back")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_cancel_add() -> ReplyKeyboardMarkup:
    """❌ Cancel + 🔙 Back — used in input-wait states from Add Account."""
    return ReplyKeyboardMarkup(
        [[KeyboardButton("❌ Cancel"), KeyboardButton("🔙 Back")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_digits() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("6 digits"), KeyboardButton("8 digits")],
            [KeyboardButton("🔙 Back")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_period() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("30 seconds"), KeyboardButton("60 seconds")],
            [KeyboardButton("🔙 Back")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_unlock() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("🔓 Unlock Vault")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_unlock_with_appeal() -> ReplyKeyboardMarkup:
    """Lock screen keyboard that includes the passcode reset appeal button."""
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("🔓 Unlock Vault")],
            [KeyboardButton("🆘 Forgot Passcode? Appeal Reset")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )




# ─────────────────────────────────────────────────────────────
# 9.  INLINE KEYBOARDS
# ─────────────────────────────────────────────────────────────
def ikb_otp_view(svc: str, uid: int = 0) -> InlineKeyboardMarkup:
    """
    BUG FIX: svc in callback_data is now always the raw name (not index).
    OTP_GET/OTP_STOP/DETAIL/DEL_ASK store index; but these buttons are
    on a live OTP message where the svc is already known, so raw is fine
    and safe (svc here is at most 64 chars; prefix + colon = ≤70 — safe).
    """
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔄 Refresh",   callback_data=f"OTP_REF:{svc}"),
            InlineKeyboardButton("⏹ Stop",       callback_data=f"OTP_STOP:{svc}"),
            InlineKeyboardButton("📋 Copy OTP",   callback_data=f"OTP_COPY:{svc}"),
        ],
        [
            InlineKeyboardButton("ℹ️ Details",   callback_data=f"DETAIL_RAW:{svc}"),
            InlineKeyboardButton("🗑 Delete",     callback_data=f"DEL_ASK_RAW:{svc}"),
            InlineKeyboardButton("⭐ Star",        callback_data=f"STAR:{svc}"),
        ],
        [
            InlineKeyboardButton("📤 Export URI", callback_data=f"EXPORT:{svc}"),
        ],
    ])


def ikb_detail(svc: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔑 Get OTP",    callback_data=f"OTP_REF:{svc}"),
            InlineKeyboardButton("✏️ Rename",     callback_data=f"RENAME_RAW:{svc}"),
        ],
        [
            InlineKeyboardButton("⭐ Star/Unstar", callback_data=f"STAR:{svc}"),
            InlineKeyboardButton("🗑 Delete",      callback_data=f"DEL_ASK_RAW:{svc}"),
        ],
        [
            InlineKeyboardButton("📤 Export URI", callback_data=f"EXPORT:{svc}"),
        ],
    ])


def ikb_del_confirm(svc: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✅ Yes, Delete", callback_data=f"DEL_OK_RAW:{svc}"),
            InlineKeyboardButton("❌ Cancel",       callback_data="DEL_CANCEL"),
        ]
    ])


def ikb_admin_reset(request_id: str) -> InlineKeyboardMarkup:
    """Admin inline keyboard shown on a reset request notification."""
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✅ Approve Reset", callback_data=f"RESET_APPROVE:{request_id}"),
            InlineKeyboardButton("❌ Deny Reset",    callback_data=f"RESET_DENY:{request_id}"),
        ],
        [
            InlineKeyboardButton("💬 Chat with User", callback_data=f"RESET_CHAT:{request_id}"),
        ],
    ])


def ikb_user_reset_agree(request_id: str) -> InlineKeyboardMarkup:
    """Inline keyboard sent to the user after admin approves."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ I Agree — Send Temp Passcode", callback_data=f"RESET_AGREE:{request_id}")]
    ])


def ikb_update_confirm(svc: str, cache_key: str) -> InlineKeyboardMarkup:
    """
    BUG FIX: callback_data now carries a short cache_key (e.g. "upd:12345678")
    instead of the raw svc name, which could exceed 64 bytes for long names.
    """
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔄 Update Secret", callback_data=f"UPD_OK:{cache_key}"),
            InlineKeyboardButton("❌ Cancel",          callback_data="DEL_CANCEL"),
        ]
    ])


def ikb_multi_qr(parsed_list: list, cache_key: str) -> InlineKeyboardMarkup:
    """Picker shown when a QR image contains multiple otpauth URIs."""
    rows = []
    for i, p in enumerate(parsed_list):
        rows.append([InlineKeyboardButton(
            f"{'🔐' if p['type']=='totp' else '🔢'} {p['svc']}",
            callback_data=f"QR_PICK:{cache_key}:{i}",
        )])
    rows.append([InlineKeyboardButton("❌ Cancel All", callback_data="DEL_CANCEL")])
    return InlineKeyboardMarkup(rows)


# ── Account list / pagination ────────────────────────────────
_acct_cache: dict[int, list] = {}   # uid → sorted svc list


def _invalidate_cache(uid: int) -> None:
    _acct_cache.pop(uid, None)


def _cache_accounts(uid: int, docs: list) -> list:
    """Sort docs (starred first, then alpha), store svc names in cache."""
    sorted_docs = sorted(
        docs,
        key=lambda x: (not x.get("starred", False), x["svc"].lower()),
    )
    _acct_cache[uid] = [d["svc"] for d in sorted_docs]
    return sorted_docs


def svc_from_index(uid: int, idx: int) -> Optional[str]:
    cache = _acct_cache.get(uid, [])
    if 0 <= idx < len(cache):
        return cache[idx]
    return None


def ikb_accounts(docs: list, prefix: str, page: int = 0,
                 uid: int = 0) -> InlineKeyboardMarkup:
    sorted_docs = _cache_accounts(uid, docs) if uid else sorted(
        docs, key=lambda x: (not x.get("starred", False), x["svc"].lower())
    )
    total     = len(sorted_docs)
    start     = page * PAGE_SIZE
    end       = start + PAGE_SIZE
    rows      = []

    for abs_idx, d in enumerate(sorted_docs[start:end], start=start):
        star  = "⭐ " if d.get("starred") else ""
        label = f"{star}🔐 {d['svc']}"
        if d.get("issuer") and d["issuer"] != d["svc"]:
            label += f"  · {d['issuer']}"
        cb = f"{prefix}:{abs_idx}"
        rows.append([InlineKeyboardButton(label, callback_data=cb)])

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️ Prev", callback_data=f"PAGE:{prefix}:{page-1}"))
    if end < total:
        nav.append(InlineKeyboardButton("▶️ Next", callback_data=f"PAGE:{prefix}:{page+1}"))
    if nav:
        rows.append(nav)
    return InlineKeyboardMarkup(rows)


# ─────────────────────────────────────────────────────────────
# 10.  PENDING UPDATE STORE
#      BUG FIX: stored server-side (not in ctx.user_data) so the pending
#      payload survives callback-query boundaries without being cleared.
# ─────────────────────────────────────────────────────────────
_pending_updates: dict[str, dict] = {}   # cache_key → parsed dict
_pending_qr:     dict[str, list]  = {}   # cache_key → list of parsed dicts

# ── Admin impersonation state ────────────────────────────────
# Maps admin's real UID → target user UID they are currently viewing as.
# This is server-side so it survives ctx.user_data.clear() calls.
_impersonation: dict[int, int] = {}   # real_admin_uid → target_uid


def _store_pending(store: dict, payload) -> str:
    key = base64.urlsafe_b64encode(os.urandom(6)).decode().rstrip("=")
    store[key] = payload
    return key


def _pop_pending(store: dict, key: str):
    return store.pop(key, None)


# ─────────────────────────────────────────────────────────────
# 11.  TEXT HELPERS
# ─────────────────────────────────────────────────────────────
def _human_age(dt: datetime) -> str:
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    delta = datetime.now(timezone.utc) - dt
    days  = delta.days
    if days == 0:
        return "today"
    if days == 1:
        return "yesterday"
    if days < 30:
        return f"{days}d ago"
    if days < 365:
        return f"{days // 30}mo ago"
    return f"{days // 365}y ago"


def home_text(uid: int, name: str) -> str:
    count   = col_accounts.count_documents({"uid": uid})
    pin_set = bool(db_get_pin(uid))
    paranoid = db_get_setting(uid, "paranoid", False)
    return (
        f"⚡ *NexAuth — 2FA Vault*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 {name}   🔐 {count} service{'s' if count != 1 else ''}\n"
        f"{'🔑' if pin_set else '🔓'} Passcode: {'Set' if pin_set else 'Not set'}\n"
        f"{'🔕 Paranoid mode ON' if paranoid else ''}\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"Auto-locks after *{SESSION_TTL // 60} min* inactivity.\n"
        f"Type /help for all commands."
    )


def otp_text(svc: str, issuer: str, secret: str,
             digits: int = 6, period: int = 30, algorithm: str = "SHA1",
             otp_type: str = "totp", counter: int = 0, starred: bool = False) -> str:
    if otp_type == "hotp":
        hotp = _make_hotp(secret, digits, counter, algorithm)
        code = hotp.at(counter)
        bar  = "🔢 HOTP"
        remaining_str = f"counter #{counter}"
    else:
        totp      = _make_totp(secret, digits, period, algorithm)
        code      = totp.now()
        remaining = period - (int(time.time()) % period)
        filled    = int(remaining / (period / 10))
        bar       = "█" * filled + "░" * (10 - filled)
        remaining_str = f"_{remaining}s left_"

    half    = digits // 2
    # FIX BUG 5: was `if digits == 6 else code` — 8-digit codes showed as raw "12345678"
    # with no spacing. Apply half-split grouping for both 6-digit and 8-digit codes.
    pretty  = f"{code[:half]} {code[half:]}"
    star    = "⭐ " if starred else ""
    return (
        f"🔐 *{star}{svc}*\n"
        f"🏢 _{issuer}_\n"
        f"━━━━━━━━━━━━━━━━\n\n"
        f"```\n{pretty}\n```\n"
        f"_(tap to copy)_\n\n"
        f"`{bar}` {remaining_str}"
    )


def detail_text(doc: dict) -> str:
    created = doc["created"]
    if created.tzinfo is None:
        created = created.replace(tzinfo=timezone.utc)
    updated = doc.get("updated")
    if updated and updated.tzinfo is None:
        updated = updated.replace(tzinfo=timezone.utc)
    age      = _human_age(created)
    added    = created.strftime("%Y-%m-%d")
    upd_line = f"\n🔄 *Updated:* `{updated.strftime('%Y-%m-%d')}`" if updated else ""
    otp_type = doc.get("type", "totp").upper()
    star     = "⭐ " if doc.get("starred") else ""
    return (
        f"ℹ️ *Account Details*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{star}🏷 *Name:*    `{doc['svc']}`\n"
        f"🏢 *Issuer:*  `{doc.get('issuer', '—')}`\n"
        f"🔢 *Digits:*  `{doc.get('digits', 6)}`\n"
        f"⏱ *Period:*  `{doc.get('period', 30)}s`\n"
        f"🔑 *Algo:*    `{doc.get('algorithm', 'SHA1')}`\n"
        f"📟 *Type:*    `{otp_type}`\n"
        f"📅 *Added:*   `{added}` _({age})_{upd_line}"
    )


def locked_text() -> str:
    return (
        f"🔒 *Vault Locked*\n\n"
        f"Session expired after {SESSION_TTL // 60} min of inactivity.\n"
        f"Tap *🔓 Unlock Vault* or enter your passcode."
    )


async def send_locked(update: Update, uid: int = 0) -> None:
    # FIX BUG 12: was always rkb_unlock() regardless of whether the user had set
    # security questions. Users locked mid-flow (e.g. cmd_digest) had no appeal
    # button even though they were eligible. Now we check db_has_security_answers()
    # and show rkb_unlock_with_appeal() when appropriate.
    # uid is optional so existing callers that don't pass it still work (no appeal).
    if uid and db_has_security_answers(uid):
        markup = rkb_unlock_with_appeal()
    else:
        markup = rkb_unlock()
    await update.effective_chat.send_message(
        locked_text(),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=markup,
    )


def _ensure_user(update: Update) -> None:
    user = update.effective_user
    if user:
        db_upsert_user(user.id, user.first_name, user.username)


# ─────────────────────────────────────────────────────────────
# 12.  AUTO-REFRESH OTP LOOP
# ─────────────────────────────────────────────────────────────
_refresh_tasks: dict[int, asyncio.Task] = {}
# Bulk tasks spawned by "Get OTP" (all accounts view) — tracked per uid as a list
_bulk_refresh_tasks: dict[int, list[asyncio.Task]] = {}


def _cancel_refresh(uid: int) -> None:
    task = _refresh_tasks.pop(uid, None)
    if task and not task.done():
        task.cancel()
    # Also cancel any bulk OTP refresh tasks
    for t in _bulk_refresh_tasks.pop(uid, []):
        if not t.done():
            t.cancel()


async def _otp_refresh_loop(
    chat_id: int, message_id: int, uid: int,
    svc: str, doc: dict, secret: str, bot,
    paranoid: bool = False,
    no_inline: bool = False,
) -> None:
    digits    = doc.get("digits", 6)
    period    = doc.get("period", 30)
    issuer    = doc.get("issuer", svc)
    algorithm = doc.get("algorithm", "SHA1")
    otp_type  = doc.get("type", "totp")
    counter   = doc.get("counter", 0)
    start_ts  = time.monotonic()

    try:
        while True:
            # Paranoid mode: delete OTP message after TTL
            if paranoid and (time.monotonic() - start_ts) >= PARANOID_TTL_S:
                try:
                    await bot.delete_message(chat_id=chat_id, message_id=message_id)
                except (BadRequest, TelegramError):
                    pass
                break

            if not session_alive(uid):
                try:
                    await bot.edit_message_text(
                        chat_id=chat_id, message_id=message_id,
                        text=locked_text(), parse_mode=ParseMode.MARKDOWN,
                        reply_markup=None,
                    )
                except (BadRequest, TelegramError):
                    pass
                break

            if otp_type == "hotp":
                # HOTP doesn't tick — stop after first display
                break

            text = otp_text(svc, issuer, secret, digits, period, algorithm)
            markup = None if no_inline else ikb_otp_view(svc)
            try:
                await bot.edit_message_text(
                    chat_id=chat_id, message_id=message_id,
                    text=text, parse_mode=ParseMode.MARKDOWN,
                    reply_markup=markup,
                )
            except BadRequest as e:
                if "not modified" not in str(e).lower():
                    log.warning("OTP refresh edit: %s", e)
            except TelegramError as e:
                log.warning("OTP refresh error: %s", e)
                break

            await asyncio.sleep(1)

    except asyncio.CancelledError:
        pass
    finally:
        _refresh_tasks.pop(uid, None)


async def start_otp_refresh(chat_id: int, message_id: int,
                             uid: int, svc: str, doc: dict, secret: str,
                             bot, paranoid: bool = False,
                             no_inline: bool = False) -> None:
    _cancel_refresh(uid)
    task = asyncio.create_task(
        _otp_refresh_loop(chat_id, message_id, uid, svc, doc, secret, bot, paranoid, no_inline)
    )
    _refresh_tasks[uid] = task


# ─────────────────────────────────────────────────────────────
# 13.  /start  /help  /restart  /digest  /admin_stats
# ─────────────────────────────────────────────────────────────
async def _require_unlock(update: Update, ctx: ContextTypes.DEFAULT_TYPE, uid: int) -> bool:
    """
    Returns True if the vault is open (session alive OR no PIN set).
    Returns False and sends the lock screen if a PIN is set and vault is locked.
    NEVER calls session_touch() when a PIN is set and the session is dead.
    """
    if session_alive(uid):
        return True
    pin_hash = db_get_pin(uid)
    if pin_hash:
        # Vault is locked — do not touch the session, redirect to lock screen
        ctx.user_data.clear()
        _cancel_refresh(uid)
        # FIX BUG 12: show appeal button if user has security questions set
        markup = rkb_unlock_with_appeal() if db_has_security_answers(uid) else rkb_unlock()
        await update.effective_chat.send_message(
            locked_text(),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=markup,
        )
        return False
    # No PIN set — safe to open session
    session_touch(uid)
    return True


async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    user = update.effective_user
    uid  = user.id
    if not rate_ok(uid):
        await update.message.reply_text("⚠️ Too many requests. Please wait.")
        return
    # SECURITY FIX: /start must not bypass PIN — check lock state first
    if not await _require_unlock(update, ctx, uid):
        return
    session_touch(uid)
    ctx.user_data.clear()
    _cancel_refresh(uid)
    await update.message.reply_text(
        f"👋 *Welcome, {user.first_name}!*\n\n" + home_text(uid, user.first_name),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_home(),
    )


async def cmd_restart(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    user = update.effective_user
    uid  = user.id
    if not rate_ok(uid):
        return
    # SECURITY FIX: /restart must not bypass PIN
    if not await _require_unlock(update, ctx, uid):
        return
    _cancel_refresh(uid)
    ctx.user_data.clear()
    session_touch(uid)
    await update.message.reply_text(
        "🔄 *Restarted.*\n\n" + home_text(uid, user.first_name),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_home(),
    )


async def cmd_help(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    uid = update.effective_user.id
    if not rate_ok(uid):
        return
    # Help is safe to show without unlocking — it contains no vault data.
    # But do NOT touch the session; a locked vault stays locked.
    text = (
        "📖 *NexAuth Help*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "*Adding Accounts*\n"
        "• ➕ Add Account → scan QR, paste URI, or enter base32 secret\n"
        "• Supports TOTP and HOTP; SHA1/SHA256/SHA512; 6 or 8 digits\n\n"
        "*Using OTPs*\n"
        "• 🔑 Get OTP → choose service → live countdown code\n"
        "• 📋 Copy OTP — sends raw digits for easy copy\n"
        "• ⏹ Stop — freeze the code display\n\n"
        "*Managing Accounts*\n"
        "• 📋 My Accounts — browse all; ⭐ starred ones sort to top\n"
        "• 🔍 Search — find by name or issuer\n"
        "• ✏️ Rename — rename any account\n"
        "• 🗑 Delete Account — with confirmation\n"
        "• 📤 Export URI — get otpauth:// string (auto-deletes in 30s)\n\n"
        "*Security*\n"
        "• 🔒 Lock Vault — manually lock\n"
        "• ⚙️ Settings → 🔑 Set Passcode — PIN-protect the vault\n"
        "• 🔕 Paranoid Mode — OTP messages delete themselves after 60s\n"
        "• Auto-locks after inactivity\n\n"
        "*Backup*\n"
        "• 💾 Backup — AES-256 encrypted token\n"
        "• 📥 Restore — paste token to restore\n\n"
        "*Commands*\n"
        "`/start` — home screen\n"
        "`/restart` — clear state & go home\n"
        "`/help` — this message\n"
        "`/digest` — monthly activity summary\n"
    )
    pin_set = bool(db_get_pin(uid))
    if pin_set and not session_alive(uid):
        keyboard = rkb_unlock()
    elif ctx.user_data.get("back") == "settings":
        keyboard = rkb_back_settings()
    else:
        keyboard = rkb_home()
    await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN, reply_markup=keyboard)


async def cmd_digest(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    uid = update.effective_user.id
    if not session_alive(uid):
        await send_locked(update, uid); return  # FIX BUG 12: pass uid for appeal button
    session_touch(uid)
    pipeline = [
        {"$match": {"uid": uid}},
        {"$group": {
            "_id": {"$dateToString": {"format": "%Y-%m", "date": "$created"}},
            "count": {"$sum": 1},
        }},
        {"$sort": {"_id": -1}},
        {"$limit": 12},
    ]
    rows = list(col_accounts.aggregate(pipeline))
    if not rows:
        await update.message.reply_text("📭 No accounts yet.", reply_markup=rkb_home())
        return
    lines = "\n".join(f"  `{r['_id']}` — {r['count']} added" for r in rows)
    await update.message.reply_text(
        f"📅 *Monthly Account Digest*\n━━━━━━━━━━━━━━━━\n{lines}",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_home(),
    )


async def cmd_broadcast(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user.id != ADMIN_ID:
        await update.message.reply_text("⛔ Admin only.")
        return

    # Fix 1: ctx.args is None when no args given, not just empty list
    args = ctx.args or []
    if not args:
        await update.message.reply_text(
            "📢 *Broadcast Usage*\n\n`/broadcast Your message here`",
            parse_mode=ParseMode.MARKDOWN,
        )
        return

    msg_text = " ".join(args)
    users    = list(col_users.find({}, {"uid": 1}))
    total    = len(users)

    if total == 0:
        await update.message.reply_text("📭 No users to broadcast to.")
        return

    # Send a progress message the admin can watch update
    progress_msg = await update.message.reply_text(
        f"📢 Broadcasting to {total} user(s)…\n`0 / {total}`",
        parse_mode=ParseMode.MARKDOWN,
    )

    sent = failed = blocked = 0
    BATCH = 25          # update progress every N users
    # Fix 2: Telegram allows ~30 msg/s globally; 1/s per chat.
    # 0.05s sleep between sends = 20/s which is safe for most bots.
    # For large lists we also throttle per-batch to stay under global limits.
    RATE_SLEEP   = 0.05   # seconds between each send
    BATCH_SLEEP  = 1.0    # extra pause every BATCH sends

    for i, u in enumerate(users, 1):
        try:
            await ctx.bot.send_message(
                u["uid"],
                f"📢 *Announcement*\n\n{msg_text}",
                parse_mode=ParseMode.MARKDOWN,
            )
            sent += 1
        except TelegramError as e:
            err = str(e).lower()
            # Fix 3: distinguish "user blocked/deleted" from real errors
            if any(x in err for x in ("blocked", "deactivated", "not found",
                                       "chat not found", "forbidden")):
                blocked += 1
            else:
                failed += 1
                log.warning("Broadcast send error uid=%s: %s", u["uid"], e)

        await asyncio.sleep(RATE_SLEEP)

        # Fix 4: live progress update every BATCH users
        if i % BATCH == 0 or i == total:
            try:
                await progress_msg.edit_text(
                    f"📢 Broadcasting… `{i} / {total}`\n"
                    f"✅ {sent}  🚫 {blocked} blocked  ❌ {failed} errors",
                    parse_mode=ParseMode.MARKDOWN,
                )
            except TelegramError:
                pass

        if i % BATCH == 0:
            await asyncio.sleep(BATCH_SLEEP)

    # Final summary
    try:
        await progress_msg.edit_text(
            f"✅ *Broadcast Complete*\n\n"
            f"• Sent     : `{sent}`\n"
            f"• Blocked  : `{blocked}` _(user blocked the bot)_\n"
            f"• Errors   : `{failed}`\n"
            f"• Total    : `{total}`",
            parse_mode=ParseMode.MARKDOWN,
        )
    except TelegramError:
        await update.message.reply_text(
            f"✅ Broadcast done — {sent}/{total} sent, {blocked} blocked, {failed} errors."
        )
    log.info("Broadcast admin=%s sent=%d blocked=%d failed=%d total=%d",
             update.effective_user.id, sent, blocked, failed, total)


async def cmd_admin_stats(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user.id != ADMIN_ID:
        await update.message.reply_text("⛔ Admin only.")
        return
    total_users    = col_users.count_documents({})
    total_accounts = col_accounts.count_documents({})
    active_sessions = col_sessions.count_documents({})
    audit_7d = col_audit.count_documents({
        "ts": {"$gte": datetime.now(timezone.utc) - timedelta(days=7)}
    })
    st = db_mongo_storage_info()
    if st["ok"]:
        bar_line  = f"\n`{st['bar']}` {st['pct_used']}" if st.get("bar") else ""
        free_line = st["free"]
        storage_section = (
            f"\n\n💾 *MongoDB Storage*\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"📦 Data size     : `{st['data']}`\n"
            f"🗄 Storage size  : `{st['storage']}`\n"
            f"🔑 Index size    : `{st['indexes']}`\n"
            f"🆓 Free space    : `{free_line}`{bar_line}\n"
            f"📂 Collections   : `{st['collections']}`\n"
            f"📄 Documents     : `{st['objects']:,}`"
        )
    else:
        storage_section = f"\n\n💾 *MongoDB Storage*: _{st.get('error', 'unavailable')}_"

    await update.message.reply_text(
        f"🛡 *Admin Stats*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"👥 Users         : `{total_users}`\n"
        f"🔐 Accounts      : `{total_accounts}`\n"
        f"🔓 Active sessions: `{active_sessions}`\n"
        f"📋 Audit 7d      : `{audit_7d}`"
        + storage_section,
        parse_mode=ParseMode.MARKDOWN,
    )


# ─────────────────────────────────────────────────────────────
# 14.  REPLY KEYBOARD MESSAGE ROUTER
# ─────────────────────────────────────────────────────────────
async def on_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)

    uid   = update.effective_user.id
    text  = (update.message.text or "").strip()
    state = ctx.user_data.get("state", "")

    if not rate_ok(uid):
        await update.message.reply_text("⚠️ Too many requests. Please wait.")
        return

    # ── BAN CHECK ───────────────────────────────────────────
    if await _check_ban(update):
        return

    # ── ADMIN PANEL ROUTER ──────────────────────────────────
    if await _handle_admin_message(update, ctx, uid, text, state):
        return

    # ── CANCEL ──────────────────────────────────────────────
    if text == "❌ Cancel":
        # Block Cancel if user is in the forced new-passcode flow
        if state in ("WAIT_RESET_NEW_PIN", "WAIT_RESET_CONFIRM_PIN"):
            await update.message.reply_text(
                "⚠️ *You must set a new passcode before continuing.*\n\n"
                "Send a new 4–8 digit PIN to proceed.",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_cancel(),
            )
            return

        ctx.user_data.clear()
        _cancel_refresh(uid)

        # SECURITY FIX: if the vault is locked (session dead) AND a PIN is set,
        # Cancel must NOT create a session or show home — send the lock screen.
        # Previously this block called session_touch() unconditionally, allowing
        # anyone to bypass the PIN by simply pressing Cancel.
        if not session_alive(uid):
            pin_hash = db_get_pin(uid)
            if pin_hash:
                # Vault is locked and PIN-protected — stay locked
                await update.message.reply_text(
                    locked_text(),
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock(),
                )
                return
            else:
                # No PIN set — safe to open a session and go home
                session_touch(uid)

        await update.message.reply_text(
            home_text(uid, update.effective_user.first_name),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )
        return

    # ── BACK ────────────────────────────────────────────────
    if text == "🔙 Back":
        # Blocked during forced passcode-change flow
        if state in ("WAIT_RESET_NEW_PIN", "WAIT_RESET_CONFIRM_PIN"):
            await update.message.reply_text(
                "⚠️ *You must set a new passcode before continuing.*\n\n"
                "Send a new 4–8 digit PIN to proceed.",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_cancel(),
            )
            return

        back_dest = ctx.user_data.get("back", "home")
        ctx.user_data.clear()
        _cancel_refresh(uid)

        # Security: if vault is locked, back must go to lock screen
        if not session_alive(uid):
            pin_hash = db_get_pin(uid)
            if pin_hash:
                await update.message.reply_text(
                    locked_text(), parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_unlock()
                )
                return
            else:
                session_touch(uid)

        if back_dest == "settings":
            pin_set  = bool(db_get_pin(uid))
            paranoid = db_get_setting(uid, "paranoid", False)
            await update.message.reply_text(
                f"⚙️ *Settings*\n\n"
                f"🔑 Passcode: {'✅ Set' if pin_set else '❌ Not set'}\n"
                f"🔕 Paranoid mode: {'✅ ON' if paranoid else '❌ OFF'}\n\n"
                f"Choose an option:",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_settings(),
            )
        elif back_dest == "add":
            await update.message.reply_text(
                "➕ *Add New TOTP Account*\n\nChoose how to add:",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_add_menu(),
            )
        else:  # "home" or anything unrecognised
            await update.message.reply_text(
                home_text(uid, update.effective_user.first_name),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_home(),
            )
        return


    if text == "🆘 Forgot Passcode? Appeal Reset":
        await _do_appeal_reset(update, ctx, uid)
        return

    # ── NEW PIN AFTER RESET (temp passcode used) ─────────────
    if state == "WAIT_RESET_NEW_PIN":
        try:
            await update.message.delete()
        except TelegramError:
            pass
        await _do_reset_new_pin(update, ctx, uid, text)
        return

    if state == "WAIT_RESET_CONFIRM_PIN":
        try:
            await update.message.delete()
        except TelegramError:
            pass
        await _do_reset_confirm_pin(update, ctx, uid, text)
        return

    # ── UNLOCK VAULT ────────────────────────────────────────
    if text == "🔓 Unlock Vault":
        pin_hash = db_get_pin(uid)
        if pin_hash:
            lockout_key = f"pin_lockout_{uid}"
            # Check in-memory lockout first (fast path)
            lockout_until = ctx.bot_data.get(lockout_key, 0)
            if time.monotonic() < lockout_until:
                remaining = int(lockout_until - time.monotonic())
                await update.message.reply_text(
                    f"🚫 *Too many wrong attempts.*\nTry again in *{remaining}s*.\n\n"
                    f"_Forgot your passcode? Tap_ *🆘 Forgot Passcode? Appeal Reset* _below._",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock_with_appeal(),
                )
                return
            # Also check DB-persisted lockout (survives restarts)
            db_lockout_str = db_get_setting(uid, "pin_lockout_until", None)
            if db_lockout_str:
                try:
                    db_lockout_dt = datetime.fromisoformat(db_lockout_str)
                    if db_lockout_dt.tzinfo is None:
                        db_lockout_dt = db_lockout_dt.replace(tzinfo=timezone.utc)
                    remaining_s = int((db_lockout_dt - datetime.now(timezone.utc)).total_seconds())
                    if remaining_s > 0:
                        # Restore into bot_data so fast path works next time
                        ctx.bot_data[lockout_key] = time.monotonic() + remaining_s
                        await update.message.reply_text(
                            f"🚫 *Too many wrong attempts.*\nTry again in *{remaining_s}s*.\n\n"
                            f"_Forgot your passcode? Tap_ *🆘 Forgot Passcode? Appeal Reset* _below._",
                            parse_mode=ParseMode.MARKDOWN,
                            reply_markup=rkb_unlock_with_appeal(),
                        )
                        return
                    else:
                        # Lockout expired — clear it
                        db_set_setting(uid, "pin_lockout_until", None)
                        db_set_setting(uid, "pin_attempts", 0)
                except (ValueError, TypeError):
                    pass
            ctx.user_data["state"] = "WAIT_PIN_UNLOCK"
            await update.message.reply_text(
                "🔑 *Enter your passcode to unlock:*",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_unlock(),
            )
        else:
            session_touch(uid)
            ctx.user_data.clear()
            db_record_unlock(uid)
            await update.message.reply_text(
                home_text(uid, update.effective_user.first_name),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_home(),
            )
        return

    # ── PIN ENTRY (unlock) ──────────────────────────────────
    if state == "WAIT_PIN_UNLOCK":
        try:
            await update.message.delete()
        except TelegramError:
            pass
        pin_hash = db_get_pin(uid)
        if pin_hash and verify_pin(text, pin_hash):
            # ── Correct PIN ──────────────────────────────────
            # Clear attempt counters from both bot_data AND DB
            ctx.bot_data.pop(f"pin_lockout_{uid}", None)
            ctx.bot_data.pop(f"pin_attempts_{uid}", None)
            db_set_setting(uid, "pin_attempts", 0)
            db_set_setting(uid, "pin_lockout_until", None)

            session_touch(uid)
            db_record_unlock(uid)
            audit(uid, "unlock")

            # ── Check if this was a temp-pin login — force passcode change ──
            temp_pending = db_get_setting(uid, "temp_pin_pending", False)
            if temp_pending:
                db_set_setting(uid, "temp_pin_pending", False)
                ctx.user_data.clear()
                ctx.user_data["state"] = "WAIT_RESET_NEW_PIN"
                audit(uid, "reset_temp_unlock")
                await update.effective_chat.send_message(
                    "✅ *Temporary passcode accepted!*\n\n"
                    "🔑 *You must now set a new permanent passcode.*\n\n"
                    "Send a new 4–8 digit PIN.\n_Message deleted immediately for security._",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_cancel(),
                )
                return

            ctx.user_data.clear()

            # ── Cancel any pending reset request — user remembered their PIN ──
            existing_req = db_get_reset_request_by_uid(uid)
            if existing_req:
                req_id = existing_req["request_id"]
                db_delete_reset_request(req_id)
                audit(uid, "reset_cancelled_by_unlock")
                task = _reset_reminder_tasks.pop(req_id, None)
                if task and not task.done():
                    task.cancel()
                _reset_admin_msg_ids.pop(req_id, None)
                try:
                    await ctx.bot.send_message(
                        chat_id=ADMIN_ID,
                        text=(
                            f"ℹ️ *Reset request cancelled*\n\n"
                            f"User `{uid}` successfully unlocked their vault with their passcode "
                            f"and no longer needs a reset. The pending request has been removed."
                        ),
                        parse_mode=ParseMode.MARKDOWN,
                    )
                except TelegramError:
                    pass
                log.info("Pending reset request cancelled — uid=%s self-unlocked", uid)

            await update.effective_chat.send_message(
                "✅ *Vault unlocked!*\n\n" + home_text(uid, update.effective_user.first_name),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_home(),
            )
        else:
            # ── Wrong PIN ────────────────────────────────────
            # Use DB-persisted counters so lockout survives bot restarts
            attempts = (db_get_setting(uid, "pin_attempts", 0) or 0) + 1
            db_set_setting(uid, "pin_attempts", attempts)

            # Also keep bot_data in sync for fast in-memory reads
            ctx.bot_data[f"pin_attempts_{uid}"] = attempts

            remaining_tries = max(0, 5 - attempts)

            if attempts >= 5:
                lockout_until = datetime.now(timezone.utc) + timedelta(seconds=PIN_LOCKOUT_S)
                db_set_setting(uid, "pin_attempts", 0)
                db_set_setting(uid, "pin_lockout_until", lockout_until.isoformat())
                ctx.bot_data[f"pin_lockout_{uid}"] = time.monotonic() + PIN_LOCKOUT_S
                ctx.bot_data[f"pin_attempts_{uid}"] = 0
                ctx.user_data.clear()
                audit(uid, "pin_lockout")
                await update.effective_chat.send_message(
                    f"🚫 *Too many wrong attempts.*\n"
                    f"Vault locked for *{PIN_LOCKOUT_S // 60} minutes*.\n\n"
                    f"_Forgot your passcode? Tap_ *🆘 Forgot Passcode? Appeal Reset* _below._",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock_with_appeal(),
                )
            else:
                # Progressive delay: 1s × attempt number (1s, 2s, 3s, 4s)
                # Slows brute-force without being annoying on an honest typo
                delay = attempts
                await asyncio.sleep(delay)
                await update.effective_chat.send_message(
                    f"❌ *Wrong passcode.* {remaining_tries} attempt{'s' if remaining_tries != 1 else ''} left.",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock(),
                )
        return

    # ── SESSION CHECK ────────────────────────────────────────
    # Appeal flow states are allowed through even with a locked vault —
    # the user can't unlock it (that's why they're appealing).
    _appeal_states = {f"WAIT_APPEAL_SECQ_{i+1}" for i in range(len(SECURITY_QUESTIONS))} | {"WAIT_APPEAL_CONFIRM"}
    if not session_alive(uid) and state not in _appeal_states:
        pin_hash = db_get_pin(uid)
        if pin_hash:
            await update.message.reply_text(
                locked_text(),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_unlock(),
            )
            return
        else:
            session_touch(uid)
            _KNOWN_BUTTONS = {
                "➕ Add Account", "🔑 Get OTP", "📋 My Accounts", "🔍 Search",
                "🔒 Lock Vault", "⚙️ Settings",
                # Settings panel
                "🗑 Delete Account", "✏️ Rename", "💾 Backup", "📥 Restore",
                "🔑 Set Passcode", "🔓 Remove Passcode",
                "🔕 Paranoid Mode", "🕐 Session Info",
                "📊 My Stats", "❓ Help",
                # Add-account sub-menu
                "📷 Scan QR Code", "🔗 Paste URI", "🔐 Enter Secret Key",
                # Navigation
                "🏠 Home", "🔙 Back", "❌ Cancel",
                # Step choices
                "6 digits", "8 digits", "30 seconds", "60 seconds",
            }
            if text not in _KNOWN_BUTTONS:
                await update.message.reply_text(
                    "👋 *Welcome to NexAuth!*\n\n" + home_text(uid, update.effective_user.first_name),
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_home(),
                )
                return

    session_touch(uid)

    # ── BLOCK ALL ACTIONS UNTIL FORCED PASSCODE CHANGE IS DONE ──
    if state in ("WAIT_RESET_NEW_PIN", "WAIT_RESET_CONFIRM_PIN"):
        try:
            await update.message.delete()
        except TelegramError:
            pass
        prompt = (
            "🔁 *Confirm new passcode*\n\nEnter the same PIN again:"
            if state == "WAIT_RESET_CONFIRM_PIN"
            else "🔑 *Set new passcode*\n\nSend a new 4–8 digit PIN.\n_Message deleted immediately for security._"
        )
        await update.effective_chat.send_message(
            "⚠️ *You must set a new passcode before you can use the vault.*\n\n" + prompt,
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return

    # ── WAIT-STATE FLOWS ────────────────────────────────────
    if state == "WAIT_RESTORE":
        await _do_restore(update, ctx, uid, text); return
    if state == "WAIT_SVC_NAME":
        await _do_save_svc_name(update, ctx, uid, text); return
    if state == "WAIT_RENAME_ADD":
        await _do_rename_add(update, ctx, uid, text); return
    if state == "WAIT_RENAME":
        await _do_rename(update, ctx, uid, text); return
    if state == "WAIT_SEARCH":
        await _do_search(update, ctx, uid, text); return
    if state == "WAIT_URI":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_add_uri(update, ctx, uid, text); return
    if state == "WAIT_KEY":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_add_key(update, ctx, uid, text); return
    if state == "WAIT_KEY_DIGITS":
        await _do_key_digits(update, ctx, uid, text); return
    if state == "WAIT_KEY_PERIOD":
        await _do_key_period(update, ctx, uid, text); return
    if state == "WAIT_SET_PIN":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_set_pin(update, ctx, uid, text); return
    if state == "WAIT_CONFIRM_PIN":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_confirm_pin(update, ctx, uid, text); return
    # Security question collection (after PIN set)
    for _qi, _qs_label in enumerate(SECURITY_QUESTIONS):
        if state == f"WAIT_SECQ_{_qi + 1}":
            await _do_secq_answer(update, ctx, uid, text, _qi)
            return
    # Security question collection during appeal (before submitting to admin)
    for _qi, _qs_label in enumerate(SECURITY_QUESTIONS):
        if state == f"WAIT_APPEAL_SECQ_{_qi + 1}":
            await _do_appeal_secq_answer(update, ctx, uid, text, _qi)
            return

    # ── MAIN MENU BUTTONS ───────────────────────────────────
    if text == "➕ Add Account":
        ctx.user_data.clear()
        ctx.user_data["back"] = "home"
        _cancel_refresh(uid)
        await update.message.reply_text(
            "➕ *Add New TOTP Account*\n\nChoose how to add:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )

    elif text == "📷 Scan QR Code":
        ctx.user_data["state"] = "WAIT_QR"
        ctx.user_data["back"] = "add"
        await update.message.reply_text(
            "📷 *Scan QR Code*\n\nSend the QR code image now.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔗 Paste URI":
        ctx.user_data["state"] = "WAIT_URI"
        ctx.user_data["back"] = "add"
        await update.message.reply_text(
            "🔗 *Paste otpauth URI*\n\nSend your `otpauth://totp/...` string.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔐 Enter Secret Key":
        ctx.user_data["state"] = "WAIT_KEY"
        ctx.user_data["back"] = "add"
        await update.message.reply_text(
            "🔐 *Enter Secret Key*\n\nSend your base32 secret key.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔑 Get OTP":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *No accounts yet.* Add one first.",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_home())
            return
        _cancel_refresh(uid)
        docs_sorted = sorted(docs, key=lambda x: (not x.get("starred", False), x["svc"].lower()))
        await update.message.reply_text(
            f"🔑 *Your OTP Codes* — {len(docs_sorted)} account{'s' if len(docs_sorted) != 1 else ''}\n"
            f"_Tap any code to copy · Codes refresh automatically_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_back_home(),
        )
        paranoid = db_get_setting(uid, "paranoid", False)
        bulk_tasks: list = []
        for doc in docs_sorted:
            svc = doc["svc"]
            full_doc = db_get(uid, svc)
            if not full_doc:
                continue
            try:
                secret = aes_decrypt(full_doc["enc"])
            except Exception:
                await update.effective_chat.send_message(
                    f"🔐 *{svc}* — decryption failed.", parse_mode=ParseMode.MARKDOWN
                )
                continue
            otp_type = full_doc.get("type", "totp")
            counter  = full_doc.get("counter", 0)
            if otp_type == "hotp":
                counter = db_hotp_increment(uid, svc)
            otp_msg = await update.effective_chat.send_message(
                otp_text(svc, full_doc.get("issuer", svc), secret,
                         full_doc.get("digits", 6), full_doc.get("period", 30),
                         full_doc.get("algorithm", "SHA1"), otp_type, counter),
                parse_mode=ParseMode.MARKDOWN,
                # No inline keyboard — clean tap-to-copy display only
            )
            # Spawn individual refresh loop without overwriting _refresh_tasks
            if otp_type == "totp":
                task = asyncio.create_task(
                    _otp_refresh_loop(
                        otp_msg.chat_id, otp_msg.message_id,
                        uid, svc, full_doc, secret, ctx.bot, paranoid,
                        no_inline=True,
                    )
                )
                bulk_tasks.append(task)
        _bulk_refresh_tasks[uid] = bulk_tasks

    elif text == "📋 My Accounts":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *Vault is empty.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_home())
            return
        ctx.user_data["back"] = "home"
        await update.message.reply_text(
            f"📋 *Your Vault* — {len(docs)} account{'s' if len(docs)!=1 else ''}\n"
            f"_Tap an account to manage it: get OTP, rename, delete, export & more._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_back_home(),
        )
        # Send the account list as a follow-up with inline buttons
        await update.effective_chat.send_message(
            "👇 Choose an account:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_accounts(docs, "DETAIL", uid=uid),
        )

    elif text == "🔍 Search":
        ctx.user_data["state"] = "WAIT_SEARCH"
        ctx.user_data["back"] = "home"
        await update.message.reply_text(
            "🔍 *Search Accounts*\n\nType any part of the name or issuer.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🗑 Delete Account":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *Nothing to delete.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_settings())
            return
        ctx.user_data["back"] = "settings"
        await update.message.reply_text(
            "🗑 *Delete Account*\n\nChoose a service:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_back_settings(),
        )
        await update.effective_chat.send_message(
            "👇 Choose an account to delete:",
            reply_markup=ikb_accounts(docs, "DEL_ASK", uid=uid),
        )

    elif text == "✏️ Rename":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *No accounts to rename.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_settings())
            return
        ctx.user_data["back"] = "settings"
        await update.message.reply_text(
            "✏️ *Rename Account*\n\nChoose a service:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_back_settings(),
        )
        await update.effective_chat.send_message(
            "👇 Choose an account to rename:",
            reply_markup=ikb_accounts(docs, "RENAME_CB", uid=uid),
        )

    elif text == "💾 Backup":
        await _do_backup(update, uid)

    elif text == "📥 Restore":
        ctx.user_data["state"] = "WAIT_RESTORE"
        ctx.user_data["back"] = "settings"
        await update.message.reply_text(
            "📥 *Restore Backup*\n\nPaste your encrypted backup string.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_settings(),
        )

    elif text == "🔒 Lock Vault":
        _cancel_refresh(uid)
        session_kill(uid)
        ctx.user_data.clear()
        audit(uid, "lock")
        await update.message.reply_text(
            "🔒 *Vault Locked.*",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )

    elif text == "⚙️ Settings":
        ctx.user_data.clear()
        ctx.user_data["back"] = "home"
        pin_set  = bool(db_get_pin(uid))
        paranoid = db_get_setting(uid, "paranoid", False)
        await update.message.reply_text(
            f"⚙️ *Settings*\n\n"
            f"🔑 Passcode: {'✅ Set' if pin_set else '❌ Not set'}\n"
            f"🔕 Paranoid mode: {'✅ ON' if paranoid else '❌ OFF'}\n\n"
            f"Choose an option:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )

    elif text == "🔑 Set Passcode":
        ctx.user_data["state"] = "WAIT_SET_PIN"
        ctx.user_data["back"] = "settings"
        await update.message.reply_text(
            "🔑 *Set Passcode*\n\nSend a 4–8 digit PIN.\n_Message deleted immediately for security._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_settings(),
        )

    elif text == "🔓 Remove Passcode":
        if not db_get_pin(uid):
            await update.message.reply_text("ℹ️ No passcode is set.", reply_markup=rkb_settings())
        else:
            db_set_pin(uid, None)
            db_set_setting(uid, "pin_attempts", 0)
            db_set_setting(uid, "pin_lockout_until", None)
            audit(uid, "pin_removed")
            await update.message.reply_text(
                "✅ *Passcode removed.*",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_settings(),
            )

    elif text == "🔕 Paranoid Mode":
        current = db_get_setting(uid, "paranoid", False)
        new_val = not current
        db_set_setting(uid, "paranoid", new_val)
        state_str = "ON ✅" if new_val else "OFF ❌"
        await update.message.reply_text(
            f"🔕 *Paranoid mode {state_str}*\n\n"
            f"{'OTP messages will auto-delete after 60s.' if new_val else 'OTP messages will persist normally.'}",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )

    elif text == "📊 My Stats":
        ctx.user_data["back"] = "settings"
        await _do_stats(update, uid)

    elif text == "🏠 Home":
        ctx.user_data.clear()
        _cancel_refresh(uid)
        await update.message.reply_text(
            home_text(uid, update.effective_user.first_name),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )

    elif text == "❓ Help":
        ctx.user_data["back"] = "settings"
        await cmd_help(update, ctx)

    elif text == "🕐 Session Info":
        session_doc = col_sessions.find_one({"uid": uid})
        ctx.user_data["back"] = "settings"
        if session_doc:
            last = session_doc.get("last")
            if last and last.tzinfo is None:
                last = last.replace(tzinfo=timezone.utc)
            elapsed = int((datetime.now(timezone.utc) - last).total_seconds()) if last else SESSION_TTL
            remaining = max(0, SESSION_TTL - elapsed)
            mins, secs = divmod(remaining, 60)
            await update.message.reply_text(
                f"🕐 *Session Info*\n\n"
                f"⏳ Time remaining: *{mins}m {secs}s*\n"
                f"⏱ Session TTL: `{SESSION_TTL}s`\n"
                f"🔒 Auto-lock after: *{SESSION_TTL // 60} min* of inactivity\n\n"
                f"_Your vault will lock automatically to protect your OTP secrets._",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_back_settings(),
            )
        else:
            await update.message.reply_text(
                "ℹ️ No active session found.",
                reply_markup=rkb_unlock(),
            )

    else:
        hints = {
            "WAIT_URI":          "📋 Please paste an `otpauth://totp/...` URI.",
            "WAIT_KEY":          "🔐 Please send your base32 secret key.",
            "WAIT_KEY_DIGITS":   "🔢 Please choose *6 digits* or *8 digits*.",
            "WAIT_KEY_PERIOD":   "⏱ Please choose *30 seconds* or *60 seconds*.",
            "WAIT_SVC_NAME":     "🏷 Please send a name for this account.",
            "WAIT_RENAME":       "✏️ Please send the new account name.",
            "WAIT_RENAME_ADD":   "✏️ Please send a unique name for this account.",
            "WAIT_SEARCH":       "🔍 Please type a search term.",
            "WAIT_RESTORE":      "📥 Please paste your encrypted backup token.",
            "WAIT_QR":           "📷 Please send the QR code image.",
        }
        hint = hints.get(state, "👆 Use the keyboard buttons to navigate.")
        back_dest = ctx.user_data.get("back", "home")
        if state in ("WAIT_KEY", "WAIT_URI", "WAIT_QR", "WAIT_KEY_DIGITS",
                     "WAIT_KEY_PERIOD", "WAIT_SVC_NAME", "WAIT_RENAME_ADD"):
            kb = rkb_cancel_add()
        elif state in ("WAIT_SET_PIN", "WAIT_CONFIRM_PIN", "WAIT_RESTORE", "WAIT_RENAME"):
            kb = rkb_cancel_settings()
        elif state:
            kb = rkb_cancel()
        else:
            kb = rkb_home()
        await update.message.reply_text(hint, parse_mode=ParseMode.MARKDOWN, reply_markup=kb)


# ─────────────────────────────────────────────────────────────
# 15.  PHOTO HANDLER — QR scan
# ─────────────────────────────────────────────────────────────
async def on_photo(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    uid   = update.effective_user.id
    state = ctx.user_data.get("state", "")

    if not rate_ok(uid):
        await update.message.reply_text("⚠️ Too many requests. Please wait.")
        return

    # BUG FIX: auto-session for no-PIN users (was missing in photo handler)
    if not session_alive(uid):
        pin_hash = db_get_pin(uid)
        if pin_hash:
            await send_locked(update, uid)  # FIX BUG 12: pass uid for appeal button
            return
        else:
            session_touch(uid)
    else:
        session_touch(uid)

    if state != "WAIT_QR":
        await update.message.reply_text(
            "📷 Tap *➕ Add Account* → *📷 Scan QR Code* first.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )
        return

    await update.effective_chat.send_chat_action(ChatAction.TYPING)
    msg = await update.message.reply_text("`⠋` _Scanning QR…_", parse_mode=ParseMode.MARKDOWN)

    photo_file  = await update.message.photo[-1].get_file()
    image_bytes = await photo_file.download_as_bytearray()
    await spin(msg, "Decoding QR", rounds=4)

    uris = decode_qr_image(bytes(image_bytes))

    if not uris:
        ctx.user_data.clear()
        await msg.edit_text(
            "❌ *No TOTP QR found.*\n\nMake sure the QR code is clear and well-lit.",
            parse_mode=ParseMode.MARKDOWN,
        )
        await update.effective_chat.send_message("Go back to add menu.", reply_markup=rkb_add_menu())
        return

    # Multiple URIs in one image → offer picker
    if len(uris) > 1:
        parsed_list = [parse_otpauth(u) for u in uris]
        parsed_list = [p for p in parsed_list if p]
        if not parsed_list:
            await msg.edit_text("❌ *QR found but all URIs are invalid.*", parse_mode=ParseMode.MARKDOWN)
            await update.effective_chat.send_message("Go back to add menu.", reply_markup=rkb_add_menu())
            return
        ck = _store_pending(_pending_qr, parsed_list)
        ctx.user_data.clear()
        await msg.edit_text(
            f"📷 Found *{len(parsed_list)}* accounts in QR. Pick one to add:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_multi_qr(parsed_list, ck),
        )
        return

    parsed = parse_otpauth(uris[0])
    if not parsed:
        ctx.user_data.clear()
        await msg.edit_text("❌ *QR found but URI is invalid.*", parse_mode=ParseMode.MARKDOWN)
        await update.effective_chat.send_message("Go back to add menu.", reply_markup=rkb_add_menu())
        return

    ctx.user_data.clear()
    paranoid = db_get_setting(uid, "paranoid", False)
    otp_msg  = await _save_and_show(msg, uid, parsed, ctx)
    if otp_msg:
        doc = db_get(uid, parsed["svc"]) or {}
        await start_otp_refresh(
            otp_msg.chat_id, otp_msg.message_id,
            uid, parsed["svc"], doc, parsed["secret"], ctx.bot, paranoid,
        )
    log.info("QR-add uid=%s svc=%s", uid, parsed.get("svc", "?"))


# ─────────────────────────────────────────────────────────────
# 16.  INLINE CALLBACK ROUTER
# ─────────────────────────────────────────────────────────────
async def on_button(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    q       = update.callback_query
    real_uid = q.from_user.id
    data    = q.data or ""

    # Always answer first — prevents "query expired" Telegram error
    await q.answer()

    # BUG FIX: rate-limit check AFTER answer(); no second q.answer() call
    if not rate_ok(real_uid):
        try:
            await q.message.reply_text("⚠️ Rate limit — slow down.")
        except TelegramError:
            pass
        return

    # ── ADMIN CALLBACK ROUTER ────────────────────────────────
    if await _handle_admin_callback(q, ctx, real_uid, data):
        return

    # ── IMPERSONATION uid SWAP ───────────────────────────────
    # FIX: _handle_impersonation_callback was defined but never called here.
    # Every inline button (OTP_GET, DETAIL, STAR, DELETE, EXPORT, PAGE, etc.)
    # was using real_uid (admin) for ALL db_get/db_delete/db_list calls, so
    # pressing any button while impersonating showed/modified the ADMIN's own
    # vault data instead of the target user's vault.
    # Solution: call _handle_impersonation_callback to swap ctx.user_data, then
    # resolve uid → target_uid via _effective_uid() before the main router runs.
    if real_uid == ADMIN_ID and is_impersonating(real_uid):
        await _handle_impersonation_callback(q, ctx, real_uid, data)
    uid = _effective_uid(real_uid)   # target_uid when impersonating, else real_uid

    if not session_alive(uid):
        pin_hash = db_get_pin(uid)
        if pin_hash:
            # Allow the user-agree callback to pass through even when locked
            if not data.startswith("RESET_AGREE:"):
                try:
                    await q.edit_message_text(locked_text(), parse_mode=ParseMode.MARKDOWN)
                except (BadRequest, TelegramError):
                    pass
                await q.message.reply_text(locked_text(), parse_mode=ParseMode.MARKDOWN,
                                            reply_markup=rkb_unlock())
                return
        else:
            session_touch(uid)

    session_touch(uid)
    paranoid = db_get_setting(uid, "paranoid", False)

    def _resolve_idx(raw: str) -> Optional[str]:
        """Numeric index → svc name. Only used for list-picker callbacks."""
        if raw.isdigit():
            return svc_from_index(uid, int(raw))
        return raw  # legacy fallback

    # ── OTP GET (from list picker) ───────────────────────────
    if data.startswith("OTP_GET:"):
        svc = _resolve_idx(data.split(":", 1)[1])
        if not svc:
            await q.message.reply_text("Session expired — please tap 🔑 Get OTP again.")
            return
        await _show_otp(q, uid, svc, ctx, paranoid)

    # ── OTP REFRESH (from OTP message buttons) ───────────────
    elif data.startswith("OTP_REF:"):
        svc = data.split(":", 1)[1]   # raw svc name — no index resolve needed
        await _show_otp(q, uid, svc, ctx, paranoid)

    # ── OTP COPY ─────────────────────────────────────────────
    elif data.startswith("OTP_COPY:"):
        svc = data.split(":", 1)[1]
        doc = db_get(uid, svc)
        if not doc:
            await q.message.reply_text("❌ Account not found."); return
        try:
            secret = aes_decrypt(doc["enc"])
        except Exception:
            await q.message.reply_text("🔐 Decryption failed."); return
        otp_type = doc.get("type", "totp")
        if otp_type == "hotp":
            counter = doc.get("counter", 0)
            code    = _make_hotp(secret, doc.get("digits", 6), counter, doc.get("algorithm", "SHA1")).at(counter)
        else:
            code = _make_totp(secret, doc.get("digits", 6), doc.get("period", 30), doc.get("algorithm", "SHA1")).now()
        copy_msg = await q.message.reply_text(f"`{code}`", parse_mode=ParseMode.MARKDOWN)
        # Auto-delete copy message after 30s
        async def _del_copy(m):
            await asyncio.sleep(30)
            try: await m.delete()
            except TelegramError: pass
        asyncio.create_task(_del_copy(copy_msg))

    # ── OTP STOP ────────────────────────────────────────────
    elif data.startswith("OTP_STOP:"):
        _cancel_refresh(uid)
        try:
            await q.edit_message_reply_markup(reply_markup=None)
        except (BadRequest, TelegramError):
            pass

    # ── DETAIL (from list picker — numeric index) ────────────
    elif data.startswith("DETAIL:"):
        svc = _resolve_idx(data.split(":", 1)[1])
        if not svc:
            await q.message.reply_text("Session expired — please tap 📋 My Accounts again.")
            return
        await _show_detail(q, uid, svc)

    # ── DETAIL (from OTP view — raw svc name) ────────────────
    elif data.startswith("DETAIL_RAW:"):
        svc = data.split(":", 1)[1]
        await _show_detail(q, uid, svc)

    # ── STAR TOGGLE ──────────────────────────────────────────
    elif data.startswith("STAR:"):
        svc = data.split(":", 1)[1]
        db_toggle_star(uid, svc)
        doc = db_get(uid, svc)
        if doc:
            await q.edit_message_text(
                detail_text(doc),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=ikb_detail(svc),
            )

    # ── EXPORT URI ──────────────────────────────────────────
    elif data.startswith("EXPORT:"):
        svc = data.split(":", 1)[1]
        doc = db_get(uid, svc)
        if not doc:
            await q.message.reply_text("Account not found."); return
        try:
            secret = aes_decrypt(doc["enc"])
        except Exception:
            await q.message.reply_text("Decryption failed."); return
        # BUG FIX: percent-encode issuer and account in URI
        enc_issuer  = quote(doc.get("issuer", svc), safe="")
        enc_svc     = quote(svc, safe="")
        uri = (
            f"otpauth://{doc.get('type','totp')}/{enc_issuer}:{enc_svc}"
            f"?secret={secret}"
            f"&issuer={enc_issuer}"
            f"&digits={doc.get('digits', 6)}"
            f"&period={doc.get('period', 30)}"
            f"&algorithm={doc.get('algorithm', 'SHA1')}"
        )
        export_msg = await q.message.reply_text(
            f"📤 *Export URI* — `{svc}`\n\n"
            f"⚠️ _Auto-deletes in {EXPORT_TTL_S}s. Keep this private!_\n\n"
            f"`{uri}`",
            parse_mode=ParseMode.MARKDOWN,
        )
        audit(uid, "export", svc)
        async def _delete_later(m):
            await asyncio.sleep(EXPORT_TTL_S)
            try: await m.delete()
            except TelegramError: pass
        asyncio.create_task(_delete_later(export_msg))

    # ── RENAME from list picker (numeric index) ───────────────
    elif data.startswith("RENAME_CB:"):
        svc = _resolve_idx(data.split(":", 1)[1])
        if not svc:
            await q.message.reply_text("Session expired — tap ✏️ Rename again."); return
        await _start_rename(q, ctx, svc)

    # ── RENAME from detail/OTP view (raw svc name) ────────────
    elif data.startswith("RENAME_RAW:"):
        svc = data.split(":", 1)[1]
        await _start_rename(q, ctx, svc)

    # ── DELETE ASK (numeric index) ───────────────────────────
    elif data.startswith("DEL_ASK:"):
        svc = _resolve_idx(data.split(":", 1)[1])
        if not svc:
            await q.message.reply_text("Session expired — tap 🗑 Delete Account again."); return
        _cancel_refresh(uid)
        await q.edit_message_text(
            f"⚠️ *Confirm Delete*\n\nPermanently remove *{svc}*?",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_del_confirm(svc),
        )

    # ── DELETE ASK (raw svc name — from OTP/detail view) ─────
    elif data.startswith("DEL_ASK_RAW:"):
        svc = data.split(":", 1)[1]
        _cancel_refresh(uid)
        await q.edit_message_text(
            f"⚠️ *Confirm Delete*\n\nPermanently remove *{svc}*?",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_del_confirm(svc),
        )

    # ── DELETE CANCEL ───────────────────────────────────────
    elif data == "DEL_CANCEL":
        try:
            await q.edit_message_reply_markup(reply_markup=None)
        except (BadRequest, TelegramError):
            pass

    # ── DELETE CONFIRM (raw svc name in callback_data) ───────
    elif data.startswith("DEL_OK_RAW:"):
        svc = data.split(":", 1)[1]
        _cancel_refresh(uid)
        if db_delete(uid, svc):
            audit(uid, "delete", svc)
            await q.edit_message_text(f"✅ *{svc}* removed from vault.", parse_mode=ParseMode.MARKDOWN)
            log.info("Deleted uid=%s svc=%s", uid, svc)
        else:
            await q.edit_message_text("❌ Account not found.")

    # ── UPDATE SECRET (BUG FIX: short cache_key in callback_data) ─
    elif data.startswith("UPD_OK:"):
        cache_key = data.split(":", 1)[1]
        parsed    = _pop_pending(_pending_updates, cache_key)
        ctx.user_data.clear()
        if not parsed:
            await q.edit_message_text("⚠️ Session lost. Please try adding the account again.")
            return
        svc    = parsed["svc"]
        secret = parsed["secret"]
        db_update_secret(uid, svc, aes_encrypt(secret),
                         parsed["issuer"], parsed["digits"], parsed["period"], parsed["algorithm"])
        doc = db_get(uid, svc) or {}
        audit(uid, "update_secret", svc)
        await q.edit_message_text(
            otp_text(svc, parsed["issuer"], secret,
                     parsed["digits"], parsed["period"], parsed["algorithm"],
                     parsed.get("type", "totp"), parsed.get("counter", 0)),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_otp_view(svc),
        )
        await start_otp_refresh(q.message.chat_id, q.message.message_id,
                                 uid, svc, doc, secret, ctx.bot, paranoid)
        log.info("Updated secret uid=%s svc=%s", uid, svc)

    # ── RENAME-ADD: save duplicate as a new name ─────────────────
    elif data.startswith("RENAME_ADD:"):
        cache_key = data.split(":", 1)[1]
        parsed    = _pop_pending(_pending_updates, cache_key)
        ctx.user_data.clear()
        if not parsed:
            await q.edit_message_text("⚠️ Session lost. Please try adding the account again.")
            return
        # Re-store so the name-entry handler can find it
        ck = _store_pending(_pending_updates, parsed)
        ctx.user_data["state"]           = "WAIT_RENAME_ADD"
        ctx.user_data["rename_add_key"]  = ck
        await q.edit_message_text(
            f"✏️ *Choose a new name* for this account\n\n"
            f"_(The existing *{parsed['svc']}* will not be changed.)_\n\n"
            f"Send a label, e.g. `{parsed['svc']} 2` or `{parsed['issuer']} (new)`:",
            parse_mode=ParseMode.MARKDOWN,
        )
        await q.message.reply_text("Type the new account name:", reply_markup=rkb_cancel())

    # ── MULTI-QR PICKER ──────────────────────────────────────
    elif data.startswith("QR_PICK:"):
        _, ck, idx_str = data.split(":", 2)
        parsed_list    = _pop_pending(_pending_qr, ck)
        if not parsed_list:
            await q.edit_message_text("⚠️ Session expired. Please scan again.")
            return
        parsed = parsed_list[int(idx_str)]
        ctx.user_data.clear()
        otp_msg = await _save_and_show(q.message, uid, parsed, ctx)
        if otp_msg:
            doc = db_get(uid, parsed["svc"]) or {}
            await start_otp_refresh(
                otp_msg.chat_id, otp_msg.message_id,
                uid, parsed["svc"], doc, parsed["secret"], ctx.bot, paranoid,
            )
        log.info("QR-pick uid=%s svc=%s", uid, parsed.get("svc", "?"))

    # ── RESET APPROVE (admin clicks) ────────────────────────
    elif data.startswith("RESET_APPROVE:"):
        if uid != ADMIN_ID:
            await q.message.reply_text("⛔ Admin only.")
            return
        request_id = data.split(":", 1)[1]
        await _do_admin_approve_reset(q, ctx, request_id)

    # ── RESET DENY (admin clicks) ───────────────────────────
    elif data.startswith("RESET_DENY:"):
        if uid != ADMIN_ID:
            await q.message.reply_text("⛔ Admin only.")
            return
        request_id = data.split(":", 1)[1]
        await _do_admin_deny_reset(q, ctx, request_id)

    # ── RESET CHAT (admin clicks to open chat with user) ────
    elif data.startswith("RESET_CHAT:"):
        if uid != ADMIN_ID:
            await q.message.reply_text("⛔ Admin only.")
            return
        request_id = data.split(":", 1)[1]
        req = db_get_reset_request(request_id)
        if not req:
            await q.answer("⚠️ Request not found.", show_alert=True)
            return
        user_id = req["uid"]
        user_name = req.get("name", "User")
        username = req.get("username")
        ulink = f"tg://user?id={user_id}"
        await q.answer("Opening chat link…", show_alert=False)
        await q.message.reply_text(
            f"💬 *Chat with {user_name}*\n\n"
            f"Tap the link below to open a direct chat:\n"
            f"[Open chat with {user_name}]({ulink})\n\n"
            f"_User ID: `{user_id}`"
            + (f"\nUsername: @{username}`" if username else "") + "_",
            parse_mode=ParseMode.MARKDOWN,
        )

    # ── RESET AGREE (user clicks after admin approves) ──────
    elif data.startswith("RESET_AGREE:"):
        request_id = data.split(":", 1)[1]
        await _do_user_agree_reset(q, ctx, uid, request_id)

    # ── APPEAL CONFIRM (user taps Submit after answering questions) ──
    elif data == "APPEAL_CONFIRM":
        qa_plain = ctx.user_data.pop("appeal_qa_plain", None)
        ctx.user_data.pop("state", None)
        if qa_plain is None:
            await q.edit_message_text("⚠️ Session lost. Please tap 🆘 Appeal Reset again.")
            return
        await q.edit_message_text("⏳ Submitting your appeal…")
        await _submit_appeal_to_admin(update, ctx, uid, qa_plain)

    # ── APPEAL CANCEL (user taps Cancel on the confirm screen) ──
    elif data == "APPEAL_CANCEL":
        ctx.user_data.clear()
        await q.edit_message_text(
            "❌ *Appeal cancelled.*\n\nTap 🔓 Unlock Vault if you remember your passcode,\n"
            "or 🆘 Forgot Passcode? Appeal Reset to try again.",
            parse_mode=ParseMode.MARKDOWN,
        )

    # ── PAGINATION ──────────────────────────────────────────
    elif data.startswith("PAGE:"):
        parts  = data.split(":", 2)
        prefix = parts[1]
        page   = int(parts[2])
        docs   = db_list(uid)
        labels = {
            "OTP_GET":   "🔑 *Get OTP Code*",
            "DEL_ASK":   "🗑 *Delete Account*",
            "RENAME_CB": "✏️ *Rename Account*",
            "DETAIL":    "📋 *Your Vault*",
        }
        label = labels.get(prefix, "🔐 *Select Account*")
        await q.edit_message_text(
            f"{label}\n\nChoose a service:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_accounts(docs, prefix, page, uid=uid),
        )


# ── Shared callback helpers ──────────────────────────────────
async def _show_otp(q, uid: int, svc: str, ctx, paranoid: bool) -> None:
    _cancel_refresh(uid)
    doc = db_get(uid, svc)
    if not doc:
        await q.edit_message_text("❌ Account not found."); return
    try:
        secret = aes_decrypt(doc["enc"])
    except Exception:
        log.exception("Decrypt error uid=%s svc=%s", uid, svc)
        await q.edit_message_text("🔐 Decryption failed."); return

    otp_type = doc.get("type", "totp")
    counter  = doc.get("counter", 0)

    # HOTP: increment counter atomically before generating code
    if otp_type == "hotp":
        counter = db_hotp_increment(uid, svc)

    await q.edit_message_text(
        otp_text(svc, doc.get("issuer", svc), secret,
                 doc.get("digits", 6), doc.get("period", 30),
                 doc.get("algorithm", "SHA1"), otp_type, counter),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_otp_view(svc),
    )
    await start_otp_refresh(
        q.message.chat_id, q.message.message_id,
        uid, svc, doc, secret, ctx.bot, paranoid,
    )


async def _show_detail(q, uid: int, svc: str) -> None:
    _cancel_refresh(uid)
    doc = db_get(uid, svc)
    if not doc:
        await q.edit_message_text("❌ Account not found."); return
    await q.edit_message_text(
        detail_text(doc),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_detail(svc),
    )


async def _start_rename(q, ctx, svc: str) -> None:
    _cancel_refresh(q.from_user.id)  # FIX BUG 1: was hardcoded 0; now uses real uid
    ctx.user_data["state"]      = "WAIT_RENAME"
    ctx.user_data["rename_svc"] = svc
    ctx.user_data["back"]       = "settings"
    await q.edit_message_text(
        f"✏️ *Rename* `{svc}`\n\nSend the new name.",
        parse_mode=ParseMode.MARKDOWN,
    )
    await q.message.reply_text("Type the new name:", reply_markup=rkb_cancel_settings())


# ─────────────────────────────────────────────────────────────
# 17.  ADD FLOWS
# ─────────────────────────────────────────────────────────────
async def _do_add_uri(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                      uid: int, text: str) -> None:
    parsed = parse_otpauth(text)
    if not parsed:
        await update.effective_chat.send_message(
            "❌ *Invalid URI.*\n\nFormat: `otpauth://totp/Label?secret=XXX&issuer=YYY`",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )
        return
    try:
        if parsed["type"] == "hotp":
            _make_hotp(parsed["secret"], parsed["digits"], parsed["counter"], parsed["algorithm"]).at(parsed["counter"])
        else:
            _make_totp(parsed["secret"], parsed["digits"], parsed["period"], parsed["algorithm"]).now()
    except Exception:
        await update.effective_chat.send_message(
            "❌ *Secret in URI is invalid.*", parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )
        return
    ctx.user_data.clear()
    paranoid = db_get_setting(uid, "paranoid", False)
    msg      = await update.effective_chat.send_message("`⠋` _Saving…_", parse_mode=ParseMode.MARKDOWN)
    otp_msg  = await _save_and_show(msg, uid, parsed, ctx)
    if otp_msg:
        doc = db_get(uid, parsed["svc"]) or {}
        await start_otp_refresh(otp_msg.chat_id, otp_msg.message_id,
                                 uid, parsed["svc"], doc, parsed["secret"], ctx.bot, paranoid)


async def _do_add_key(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                      uid: int, text: str) -> None:
    secret = parse_b32(text)
    if not secret:
        await update.effective_chat.send_message(
            "❌ *Invalid base32 secret.*\n\nOnly A–Z and 2–7 characters are valid.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )
        return
    try:
        pyotp.TOTP(secret).now()
    except Exception:
        await update.effective_chat.send_message(
            "❌ *Secret is invalid.*", parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )
        return
    ctx.user_data["pending_secret"] = secret
    ctx.user_data["state"]          = "WAIT_KEY_DIGITS"
    ctx.user_data["back"]           = "add"
    await update.effective_chat.send_message(
        "🔢 *How many digits?*\n\nMost services use 6.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_digits(),
    )


async def _do_key_digits(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                          uid: int, text: str) -> None:
    if text == "6 digits":
        ctx.user_data["pending_digits"] = 6
    elif text == "8 digits":
        ctx.user_data["pending_digits"] = 8
    else:
        await update.effective_chat.send_message(
            "❌ Please choose *6 digits* or *8 digits*.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_digits(),
        )
        return
    ctx.user_data["state"] = "WAIT_KEY_PERIOD"
    await update.effective_chat.send_message(
        "⏱ *Token refresh period?*\n\nMost services use 30 seconds.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_period(),
    )


async def _do_key_period(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                          uid: int, text: str) -> None:
    if text == "30 seconds":
        ctx.user_data["pending_period"] = 30
    elif text == "60 seconds":
        ctx.user_data["pending_period"] = 60
    else:
        await update.effective_chat.send_message(
            "❌ Please choose *30 seconds* or *60 seconds*.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_period(),
        )
        return
    ctx.user_data["state"] = "WAIT_SVC_NAME"
    ctx.user_data["back"]  = "add"
    await update.effective_chat.send_message(
        "🏷 *Name this account*\n\nSend a label (e.g. `GitHub`, `Gmail`):",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel_add(),
    )


async def _do_save_svc_name(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                             uid: int, text: str) -> None:
    try:
        await update.message.delete()
    except TelegramError:
        pass
    svc = text.strip()[:64]
    if not _SVC_RE.match(svc):
        await update.effective_chat.send_message(
            "❌ *Invalid name.* Use letters, digits, spaces, `-`, `_`, `.`, `@`",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return
    secret  = ctx.user_data.pop("pending_secret", None)
    digits  = ctx.user_data.pop("pending_digits", 6)
    period  = ctx.user_data.pop("pending_period", 30)
    ctx.user_data.clear()
    if not secret:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return
    parsed  = {"svc": svc, "issuer": svc, "secret": secret,
                "digits": digits, "period": period, "algorithm": "SHA1",
                "type": "totp", "counter": 0}
    paranoid = db_get_setting(uid, "paranoid", False)
    msg      = await update.effective_chat.send_message("`⠋` _Saving…_", parse_mode=ParseMode.MARKDOWN)
    otp_msg  = await _save_and_show(msg, uid, parsed, ctx)
    if otp_msg:
        doc = db_get(uid, svc) or {}
        await start_otp_refresh(otp_msg.chat_id, otp_msg.message_id,
                                 uid, svc, doc, secret, ctx.bot, paranoid)


async def _do_rename_add(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                         uid: int, text: str) -> None:
    """
    Called when the user picks a new name for a duplicate-svc account.
    Retrieves the pending parsed dict, swaps the svc name, and re-tries
    _save_and_show with the new name.
    """
    try:
        await update.message.delete()
    except TelegramError:
        pass

    new_svc = text.strip()[:64]
    if not _SVC_RE.match(new_svc):
        await update.effective_chat.send_message(
            "❌ *Invalid name.* Use letters, digits, spaces, `-`, `_`, `.`, `@`",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return

    ck = ctx.user_data.pop("rename_add_key", None)
    ctx.user_data.clear()

    if not ck:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return

    parsed = _pop_pending(_pending_updates, ck)
    if not parsed:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return

    # Override svc with the user-chosen name
    parsed = dict(parsed)
    parsed["svc"] = new_svc

    paranoid = db_get_setting(uid, "paranoid", False)
    msg      = await update.effective_chat.send_message("`⠋` _Saving…_", parse_mode=ParseMode.MARKDOWN)
    otp_msg  = await _save_and_show(msg, uid, parsed, ctx)
    if otp_msg:
        doc = db_get(uid, new_svc) or {}
        await start_otp_refresh(
            otp_msg.chat_id, otp_msg.message_id,
            uid, new_svc, doc, parsed["secret"], ctx.bot, paranoid,
        )


async def _save_and_show(msg, uid: int, parsed: dict, ctx=None):
    """
    Encrypt, save, show first OTP.

    FIX: When db_add returns False (DuplicateKeyError), we now check whether
    the stored encrypted secret actually differs from the new one before
    offering an update.  We also offer a third option — "Add with different
    name" — so re-adding a deleted account or adding two accounts from the
    same issuer is never stuck in an infinite "already exists" loop.

    Returns otp_msg on success (new add OR update-in-place), None otherwise.
    """
    await spin(msg, "Encrypting & saving")

    enc_new = aes_encrypt(parsed["secret"])

    ok = db_add(
        uid, parsed["svc"], parsed["issuer"],
        enc_new,
        parsed.get("digits", 6), parsed.get("period", 30),
        parsed.get("algorithm", "SHA1"),
        parsed.get("type", "totp"), parsed.get("counter", 0),
    )

    if ok:
        # Happy path — new account saved
        await msg.edit_text(
            f"✅ *{parsed['svc']}* added to vault!",
            parse_mode=ParseMode.MARKDOWN,
        )
        audit(uid, "add", parsed["svc"])
        otp_str = otp_text(
            parsed["svc"], parsed["issuer"], parsed["secret"],
            parsed.get("digits", 6), parsed.get("period", 30),
            parsed.get("algorithm", "SHA1"),
            parsed.get("type", "totp"), parsed.get("counter", 0),
        )
        otp_msg = await msg.reply_text(
            otp_str + "\n\n🔄 _Auto-refreshing..._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_otp_view(parsed["svc"]),
        )
        log.info("Added uid=%s svc=%s", uid, parsed["svc"])
        return otp_msg

    # ── Duplicate detected ──────────────────────────────────────
    # Check whether the existing record has the SAME secret already
    existing_doc = db_get(uid, parsed["svc"])

    same_secret = False
    if existing_doc:
        try:
            existing_secret = aes_decrypt(existing_doc["enc"])
            same_secret = (existing_secret == parsed["secret"])
        except Exception:
            pass  # decryption failure → treat as different secret

    # Store the full parsed payload for both UPD_OK and RENAME_ADD callbacks
    ck = _store_pending(_pending_updates, parsed)

    if same_secret:
        # Secret is identical — no need to update; just show OTP directly
        await msg.edit_text(
            f"ℹ️ *{parsed['svc']}* is already in your vault with the same secret.\n\n"
            f"Showing your existing OTP:",
            parse_mode=ParseMode.MARKDOWN,
        )
        if existing_doc:
            try:
                secret_dec = aes_decrypt(existing_doc["enc"])
                otp_str = otp_text(
                    parsed["svc"], existing_doc.get("issuer", parsed["svc"]),
                    secret_dec,
                    existing_doc.get("digits", 6), existing_doc.get("period", 30),
                    existing_doc.get("algorithm", "SHA1"),
                    existing_doc.get("type", "totp"), existing_doc.get("counter", 0),
                )
                otp_msg = await msg.reply_text(
                    otp_str + "\n\n🔄 _Auto-refreshing..._",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=ikb_otp_view(parsed["svc"]),
                )
                log.info("Re-add same-secret uid=%s svc=%s — showing existing OTP", uid, parsed["svc"])
                return otp_msg
            except Exception:
                pass
        return None

    else:
        # Secret differs — offer update OR rename-add
        await msg.edit_text(
            f"⚠️ *{parsed['svc']}* already exists in your vault with a *different* secret.\n\n"
            f"What would you like to do?",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("🔄 Update Secret",   callback_data=f"UPD_OK:{ck}"),
                    InlineKeyboardButton("✏️ Save as New Name", callback_data=f"RENAME_ADD:{ck}"),
                ],
                [
                    InlineKeyboardButton("❌ Cancel", callback_data="DEL_CANCEL"),
                ],
            ]),
        )
        return None


# ─────────────────────────────────────────────────────────────
# 18.  RENAME FLOW
# ─────────────────────────────────────────────────────────────
async def _do_rename(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                     uid: int, text: str) -> None:
    try:
        await update.message.delete()
    except TelegramError:
        pass
    new_svc = text.strip()[:64]
    if not _SVC_RE.match(new_svc):
        await update.effective_chat.send_message(
            "❌ *Invalid name.*", parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_cancel()
        )
        return
    old_svc = ctx.user_data.pop("rename_svc", None)
    ctx.user_data.clear()
    if not old_svc:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return
    # BUG FIX: db_rename now properly handles DuplicateKeyError
    if db_rename(uid, old_svc, new_svc):
        audit(uid, "rename", f"{old_svc}->{new_svc}")
        await update.effective_chat.send_message(
            f"✅ Renamed *{old_svc}* → *{new_svc}*",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )
        log.info("Renamed uid=%s %s->%s", uid, old_svc, new_svc)
    else:
        await update.effective_chat.send_message(
            f"❌ *Rename failed.* `{new_svc}` may already exist.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )


# ─────────────────────────────────────────────────────────────
# 19.  SEARCH FLOW
# ─────────────────────────────────────────────────────────────
async def _do_search(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                     uid: int, query: str) -> None:
    ctx.user_data.clear()
    results = db_search(uid, query)
    if not results:
        await update.message.reply_text(
            f"🔍 No accounts matching *{query}*.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )
        return
    await update.message.reply_text(
        f"🔍 Found *{len(results)}* result{'s' if len(results)!=1 else ''} for `{query}`:\n"
        f"_Tap to view details._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_accounts(results, "DETAIL", uid=uid),
    )


# ─────────────────────────────────────────────────────────────
# 20.  BACKUP & RESTORE
# ─────────────────────────────────────────────────────────────
async def _do_backup(update: Update, uid: int) -> None:
    docs = list(col_accounts.find(
        {"uid": uid},
        {"svc": 1, "enc": 1, "issuer": 1, "digits": 1, "period": 1,
         "algorithm": 1, "type": 1, "counter": 1, "created": 1, "_id": 0},
    ))
    if not docs:
        await update.message.reply_text("📭 Nothing to back up.", reply_markup=rkb_home())
        return
    msg = await update.message.reply_text("`⠋` _Encrypting…_", parse_mode=ParseMode.MARKDOWN)
    await spin(msg, "Encrypting backup")
    payload = json.dumps([
        {"svc": d["svc"], "enc": d["enc"], "issuer": d.get("issuer", ""),
         "digits": d.get("digits", 6), "period": d.get("period", 30),
         "algorithm": d.get("algorithm", "SHA1"),
         "type": d.get("type", "totp"), "counter": d.get("counter", 0),
         "ts": d["created"].isoformat()}
        for d in docs
    ])
    token = aes_encrypt(payload)
    audit(uid, "backup", str(len(docs)))
    backup_msg = await msg.edit_text(
        f"💾 *Encrypted Backup*\n━━━━━━━━━━━━━━━━━━━━\n"
        f"🔐 {len(docs)} account{'s' if len(docs)!=1 else ''}\n\n"
        f"`{token}`\n\n"
        f"⚠️ _Copy this now — message deletes in {BACKUP_TTL_S}s!_",
        parse_mode=ParseMode.MARKDOWN,
    )

    # Auto-delete the backup token after BACKUP_TTL_S seconds
    async def _delete_backup(m):
        await asyncio.sleep(BACKUP_TTL_S)
        try:
            await m.delete()
        except TelegramError:
            pass

    asyncio.create_task(_delete_backup(backup_msg))


async def _do_restore(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                      uid: int, token: str) -> None:
    try:
        await update.message.delete()
    except TelegramError:
        pass
    ctx.user_data.clear()
    msg = await update.effective_chat.send_message("`⠋` _Decrypting…_", parse_mode=ParseMode.MARKDOWN)
    await spin(msg, "Restoring backup")
    try:
        entries = json.loads(aes_decrypt(token))
    except Exception:
        await msg.edit_text("❌ Invalid or corrupted backup token.")
        await update.effective_chat.send_message("Back to home.", reply_markup=rkb_home())
        return
    restored = skipped = 0
    for e in entries:
        if not e.get("svc") or not e.get("enc"):
            skipped += 1
            continue
        try:
            col_accounts.update_one(
                {"uid": uid, "svc": e["svc"]},
                {"$setOnInsert": {
                    "uid": uid, "svc": e["svc"], "enc": e["enc"],
                    "issuer": e.get("issuer", e["svc"]),
                    "digits": e.get("digits", 6), "period": e.get("period", 30),
                    "algorithm": e.get("algorithm", "SHA1"),
                    "type": e.get("type", "totp"), "counter": e.get("counter", 0),
                    "starred": False,
                    "created": datetime.now(timezone.utc),
                }},
                upsert=True,
            )
            restored += 1
        except Exception:
            skipped += 1
    _invalidate_cache(uid)
    audit(uid, "restore", f"ok={restored} skip={skipped}")
    await msg.edit_text(
        f"✅ *Restore Complete*\n\n• Restored : {restored}\n• Skipped  : {skipped}",
        parse_mode=ParseMode.MARKDOWN,
    )
    await update.effective_chat.send_message("Back to home.", reply_markup=rkb_home())
    log.info("Restore uid=%s ok=%d skip=%d", uid, restored, skipped)


# ─────────────────────────────────────────────────────────────
# 21.  PASSCODE FLOWS
# ─────────────────────────────────────────────────────────────
async def _do_set_pin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                      uid: int, text: str) -> None:
    if not _PIN_RE.match(text):
        await update.effective_chat.send_message(
            "❌ *Invalid PIN.* Enter 4–8 digits only.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return
    ctx.user_data["pending_pin"] = text
    ctx.user_data["state"]       = "WAIT_CONFIRM_PIN"
    ctx.user_data["back"]        = "settings"
    await update.effective_chat.send_message(
        "🔁 *Confirm passcode*\n\nEnter the same PIN again:",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel_settings(),
    )




async def _do_secq_answer(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                           uid: int, text: str, q_index: int) -> None:
    """Collect user answer for security question q_index (0-based)."""
    try:
        await update.message.delete()
    except TelegramError:
        pass

    answers_key = "secq_answers"
    answers = ctx.user_data.setdefault(answers_key, [])
    answers.append(text)

    next_index = q_index + 1
    if next_index < len(SECURITY_QUESTIONS):
        ctx.user_data["state"] = f"WAIT_SECQ_{next_index + 1}"
        await update.effective_chat.send_message(
            f"✅ Saved.\n\n"
            f"*Question {next_index + 1} of {len(SECURITY_QUESTIONS)}:*\n"
            f"_{SECURITY_QUESTIONS[next_index]}_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_settings(),
        )
    else:
        # All answers collected — save and finish
        db_save_security_answers(uid, answers)
        ctx.user_data.clear()
        audit(uid, "security_questions_set")
        log.info("Security questions set uid=%s", uid)
        await update.effective_chat.send_message(
            "🛡 *Security questions saved!*\n\n"
            "Your vault is now locked. Please unlock it with your new passcode.\n\n"
            "_These answers will be used to verify your identity during a passcode reset appeal._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )


async def _do_confirm_pin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                          uid: int, text: str) -> None:
    pending = ctx.user_data.pop("pending_pin", None)
    if not pending:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return
    if text != pending:
        ctx.user_data.clear()
        await update.effective_chat.send_message(
            "❌ *PINs do not match.* Try again via ⚙️ Settings → 🔑 Set Passcode.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )
        return
    db_set_pin(uid, hash_pin(pending))
    session_kill(uid)
    ctx.user_data.clear()
    log.info("PIN set uid=%s — session killed, collecting security questions", uid)

    # ── Proceed to security question setup ──────────────────
    n = len(SECURITY_QUESTIONS)
    q_word = "question" if n == 1 else "questions"
    ctx.user_data["state"]       = "WAIT_SECQ_1"
    ctx.user_data["back"]        = "settings"
    await update.effective_chat.send_message(
        "✅ *Passcode set!*\n\n"
        f"🔒 For account recovery, please answer *{n} security {q_word}*.\n"
        "These will be used to verify your identity if you ever forget your passcode.\n\n"
        f"*Question 1 of {n}:*\n"
        f"_{SECURITY_QUESTIONS[0]}_",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel_settings(),
    )


# ─────────────────────────────────────────────────────────────
# 22a.  PASSCODE RESET FLOW
# ─────────────────────────────────────────────────────────────
import random
import string

def _generate_temp_pin(length: int = 8) -> str:
    """Generate a random numeric temporary passcode."""
    return "".join(random.choices(string.digits, k=length))


async def _do_appeal_reset(update: Update, ctx: ContextTypes.DEFAULT_TYPE, uid: int) -> None:
    """User taps 'Forgot Passcode? Appeal Reset' on the lock screen."""
    pin_hash = db_get_pin(uid)
    if not pin_hash:
        await update.effective_chat.send_message(
            "ℹ️ You don't have a passcode set — nothing to reset.\n\nTap 🔓 Unlock Vault to continue.",
            reply_markup=rkb_unlock(),
        )
        return

    # Check if a pending request already exists
    existing = db_get_reset_request_by_uid(uid)
    if existing:
        await update.effective_chat.send_message(
            "⏳ *Reset Request Already Pending*\n\n"
            "You have already submitted a reset request.\n"
            "Please wait for the admin to review it.\n\n"
            "If you remember your passcode, tap *🔓 Unlock Vault*.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )
        return

    # If user never set security questions, submit directly with a note to admin
    if not db_has_security_answers(uid):
        await _submit_appeal_to_admin(update, ctx, uid, qa_plain=[])
        return

    # Start the security question collection flow
    ctx.user_data["appeal_answers"] = []
    ctx.user_data["state"] = "WAIT_APPEAL_SECQ_1"
    await update.effective_chat.send_message(
        "🆘 *Passcode Reset Appeal*\n\n"
        "Please answer your security questions so the admin can verify your identity.\n\n"
        f"*Question 1 of {len(SECURITY_QUESTIONS)}:*\n"
        f"_{SECURITY_QUESTIONS[0]}_",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel(),
    )


async def _do_appeal_secq_answer(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                  uid: int, text: str, q_index: int) -> None:
    """Collect appeal answer for security question q_index (0-based)."""
    # FIX BUG 11: delete the user's answer message immediately — the answer is
    # sensitive (e.g. email address). Without this it stays visible in Telegram
    # chat history forever. Same delete pattern used by WAIT_SET_PIN handler.
    try:
        await update.message.delete()
    except TelegramError:
        pass

    answers = ctx.user_data.setdefault("appeal_answers", [])
    answers.append(text)

    next_index = q_index + 1
    if next_index < len(SECURITY_QUESTIONS):
        ctx.user_data["state"] = f"WAIT_APPEAL_SECQ_{next_index + 1}"
        await update.effective_chat.send_message(
            f"*Question {next_index + 1} of {len(SECURITY_QUESTIONS)}:*\n"
            f"_{SECURITY_QUESTIONS[next_index]}_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return

    # All answers collected — go straight to confirm, no local verification
    collected_answers = ctx.user_data.pop("appeal_answers", [])
    ctx.user_data.pop("state", None)

    qa_plain = [
        {"q": SECURITY_QUESTIONS[i], "a": collected_answers[i]}
        for i in range(len(SECURITY_QUESTIONS))
    ]
    ctx.user_data["appeal_qa_plain"] = qa_plain
    ctx.user_data["state"] = "WAIT_APPEAL_CONFIRM"
    qa_display = "\n".join(
        f"  *Q{i+1}:* {qa_plain[i]['q']}\n  *A:* `{qa_plain[i]['a']}`"
        for i in range(len(qa_plain))
    )
    await update.effective_chat.send_message(
        "📋 *Your answers:*\n\n"
        + qa_display + "\n\n"
        "These answers (alongside your originally saved answers) will be sent to the admin for comparison.\n\n"
        "Tap *✅ Submit Appeal* to send, or ❌ Cancel to abort.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Submit Appeal", callback_data="APPEAL_CONFIRM")],
            [InlineKeyboardButton("❌ Cancel", callback_data="APPEAL_CANCEL")],
        ]),
    )


async def _submit_appeal_to_admin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                   uid: int, qa_plain: list) -> None:
    """Create a reset request and notify the admin with the Q&A."""
    user = update.effective_user
    request_id = db_create_reset_request_with_qa(uid, user.first_name, user.username, qa_plain)
    audit(uid, "reset_appeal")

    # Tell user their request was submitted
    await update.effective_chat.send_message(
        "🆘 *Passcode Reset Request Submitted*\n\n"
        "Your appeal has been sent to the admin for review.\n\n"
        "The admin may send you a message to verify your identity. "
        "Please respond promptly and honestly.\n\n"
        "Once approved you will receive further instructions here.\n\n"
        "_You can still try to unlock with your passcode while waiting._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_unlock(),
    )

    # Build admin message with Q&A comparison section
    uname_str = f"@{user.username}" if user.username else "_(no username)_"
    qa_section = ""
    if qa_plain:
        stored_plain = db_get_security_answers_plain(uid) or []
        lines = []
        for i, item in enumerate(qa_plain):
            stored_ans = stored_plain[i] if i < len(stored_plain) else "_(not stored)_"
            lines.append(
                f"*Q{i+1}:* {item['q']}\n"
                f"  📂 *Stored answer:*  `{stored_ans}`\n"
                f"  ✏️ *User's answer:* `{item['a']}`"
            )
        qa_section = "\n\n🔍 *Security Q&A Comparison:*\n" + "\n\n".join(lines)
    else:
        qa_section = "\n\n⚠️ _No security questions were set for this user._"

    try:
        admin_msg = await ctx.bot.send_message(
            chat_id=ADMIN_ID,
            text=(
                "🔔 *Passcode Reset Request*\n"
                "━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"👤 *Name:*     {user.first_name}\n"
                f"🔗 *Username:* {uname_str}\n"
                f"🆔 *User ID:*  `{uid}`\n"
                f"🕐 *Time:*     {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}"
                + qa_section + "\n\n"
                "Tap ✅ Approve or ❌ Deny, or 💬 Chat to talk to the user first."
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_admin_reset(request_id),
        )
        _reset_admin_msg_ids[request_id] = admin_msg.message_id
        log.info("Reset appeal uid=%s request_id=%s — admin notified", uid, request_id)

        # ── Auto-reminder every 30 s while pending ──────────
        async def _admin_reminder_loop(req_id: str, first_msg_id: int,
                                       u_first_name: str, u_username,
                                       u_uid: int, qa_sec: str) -> None:
            old_msg_id = first_msg_id
            uname_display = f"@{u_username}" if u_username else "_(no username)_"
            attempt = 1
            while True:
                await asyncio.sleep(30)
                req_check = db_get_reset_request(req_id)
                if not req_check or req_check.get("status") != "pending":
                    _reset_reminder_tasks.pop(req_id, None)
                    _reset_admin_msg_ids.pop(req_id, None)
                    return
                attempt += 1
                try:
                    new_msg = await ctx.bot.send_message(
                        chat_id=ADMIN_ID,
                        text=(
                            f"🔔 *Passcode Reset Request* _(reminder #{attempt})_\n"
                            "━━━━━━━━━━━━━━━━━━━━━━━━\n"
                            f"👤 *Name:*     {u_first_name}\n"
                            f"🔗 *Username:* {uname_display}\n"
                            f"🆔 *User ID:*  `{u_uid}`\n"
                            f"🕐 *Time:*     {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}"
                            + qa_sec + "\n\n"
                            "⚠️ _This request is still awaiting your decision._\n"
                            "Please tap ✅ Approve or ❌ Deny below."
                        ),
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=ikb_admin_reset(req_id),
                    )
                    _reset_admin_msg_ids[req_id] = new_msg.message_id
                    log.info("Reset reminder #%d sent uid=%s request_id=%s", attempt, u_uid, req_id)
                except TelegramError as te:
                    log.warning("Could not send reset reminder: %s", te)
                    _reset_reminder_tasks.pop(req_id, None)
                    return
                await asyncio.sleep(10)
                try:
                    await ctx.bot.delete_message(chat_id=ADMIN_ID, message_id=old_msg_id)
                except TelegramError:
                    pass
                old_msg_id = new_msg.message_id

        task = asyncio.create_task(
            _admin_reminder_loop(request_id, admin_msg.message_id,
                                 user.first_name, user.username, uid, qa_section)
        )
        _reset_reminder_tasks[request_id] = task

    except TelegramError as e:
        log.error("Could not notify admin of reset request uid=%s: %s", uid, e)
        await update.effective_chat.send_message(
            "⚠️ Could not reach the admin right now. Please try again later.",
            reply_markup=rkb_unlock(),
        )
        db_delete_reset_request(request_id)


async def _do_admin_approve_reset(q, ctx, request_id: str) -> None:
    """Admin taps Approve on the reset notification."""
    req = db_get_reset_request(request_id)
    if not req:
        await q.edit_message_text("⚠️ Request not found or already processed.")
        return
    if req["status"] != "pending":
        await q.edit_message_text(f"ℹ️ Request already {req['status']}.")
        return

    db_update_reset_status(request_id, "approved")
    audit(req["uid"], "reset_approved")

    # Stop the auto-reminder loop — admin has acted
    task = _reset_reminder_tasks.pop(request_id, None)
    if task and not task.done():
        task.cancel()
    _reset_admin_msg_ids.pop(request_id, None)

    # Tell admin
    await q.edit_message_text(
        q.message.text + "\n\n✅ *You approved this request.* The user has been notified.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=None,
    )

    # Notify user with Agree button
    try:
        await ctx.bot.send_message(
            chat_id=req["uid"],
            text=(
                "✅ *Your Passcode Reset Has Been Approved!*\n\n"
                "The admin has verified your identity and approved your request.\n\n"
                "🔐 *What happens next:*\n"
                "• Tap *I Agree* below to confirm you want to proceed\n"
                "• Your temporary passcode will be sent *immediately*\n"
                "• Use that temporary passcode to unlock your vault\n"
                "• You will then be prompted to set a new permanent passcode\n\n"
                "⚠️ _Do not share the temporary passcode with anyone._"
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_user_reset_agree(request_id),
        )
        log.info("Reset approved uid=%s request_id=%s", req["uid"], request_id)
    except TelegramError as e:
        log.error("Could not notify user of reset approval uid=%s: %s", req["uid"], e)


async def _do_admin_deny_reset(q, ctx, request_id: str) -> None:
    """Admin taps Deny on the reset notification."""
    req = db_get_reset_request(request_id)
    if not req:
        await q.edit_message_text("⚠️ Request not found or already processed.")
        return
    if req["status"] != "pending":
        await q.edit_message_text(f"ℹ️ Request already {req['status']}.")
        return

    db_update_reset_status(request_id, "denied")
    audit(req["uid"], "reset_denied")

    # Stop the auto-reminder loop — admin has acted
    task = _reset_reminder_tasks.pop(request_id, None)
    if task and not task.done():
        task.cancel()
    _reset_admin_msg_ids.pop(request_id, None)

    await q.edit_message_text(
        q.message.text + "\n\n❌ *You denied this request.* The user has been notified.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=None,
    )

    try:
        await ctx.bot.send_message(
            chat_id=req["uid"],
            text=(
                "❌ *Passcode Reset Request Denied*\n\n"
                "The admin was unable to verify your identity and has denied your reset request.\n\n"
                "If you believe this is a mistake, please contact the admin directly.\n\n"
                "If you remember your passcode, tap *🔓 Unlock Vault* to continue."
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock_with_appeal(),
        )
        log.info("Reset denied uid=%s request_id=%s", req["uid"], request_id)
    except TelegramError as e:
        log.error("Could not notify user of reset denial uid=%s: %s", req["uid"], e)


async def _do_user_agree_reset(q, ctx, uid: int, request_id: str) -> None:
    """User taps 'I Agree — Send Temp Passcode' after admin approves."""
    req = db_get_reset_request(request_id)
    if not req:
        await q.edit_message_text("⚠️ Reset request not found or has expired.")
        return
    if req["uid"] != uid:
        await q.answer("⛔ This button is not for you.", show_alert=True)
        return
    if req["status"] != "approved":
        await q.edit_message_text(
            "⚠️ This request is no longer active. Please submit a new appeal if needed."
        )
        return

    db_update_reset_status(request_id, "agreed")
    audit(uid, "reset_agreed")

    # Generate and set temp pin immediately
    temp_pin = _generate_temp_pin(8)
    db_set_pin(uid, hash_pin(temp_pin))
    db_set_setting(uid, "temp_pin_pending", True)
    db_delete_reset_request(request_id)
    audit(uid, "reset_temp_pin_sent")
    log.info("Reset agreed — temp pin sent immediately uid=%s request_id=%s", uid, request_id)

    await q.edit_message_text(
        "✅ *Agreed! Your temporary passcode is below.*\n\n"
        "Use it right away to unlock your vault.",
        parse_mode=ParseMode.MARKDOWN,
    )

    try:
        temp_msg = await ctx.bot.send_message(
            chat_id=uid,
            text=(
                "🔑 *Your Temporary Passcode*\n"
                "━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
                f"`{temp_pin}`\n\n"
                "_(tap to copy)_\n\n"
                "⚠️ *Important:*\n"
                "• Use this code to unlock your vault *right now*\n"
                "• You will be required to set a new permanent passcode immediately\n"
                "• This message will be deleted in *60 seconds*\n"
                "• Never share this code with anyone"
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )
        # Auto-delete temp pin message after 60 s
        async def _del_temp_msg(m):
            await asyncio.sleep(60)
            try:
                await m.delete()
            except TelegramError:
                pass
        asyncio.create_task(_del_temp_msg(temp_msg))
    except TelegramError as e:
        log.error("Could not send temp pin uid=%s: %s", uid, e)


async def _do_reset_new_pin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                             uid: int, text: str) -> None:
    """User sets a new PIN after using temp passcode."""
    if not _PIN_RE.match(text):
        await update.effective_chat.send_message(
            "❌ *Invalid PIN.* Enter 4–8 digits only.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return
    ctx.user_data["pending_reset_pin"] = text
    ctx.user_data["state"] = "WAIT_RESET_CONFIRM_PIN"
    await update.effective_chat.send_message(
        "🔁 *Confirm new passcode*\n\nEnter the same PIN again:",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel(),
    )


async def _do_reset_confirm_pin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                 uid: int, text: str) -> None:
    """User confirms their new PIN after reset."""
    pending = ctx.user_data.pop("pending_reset_pin", None)
    ctx.user_data.clear()
    if not pending:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return
    if text != pending:
        # FIX BUG 2: vault is still locked during post-reset flow; rkb_settings() let
        # users navigate without a session. Restore state so they can retry instead.
        ctx.user_data["state"] = "WAIT_RESET_CONFIRM_PIN"
        ctx.user_data["pending_reset_pin"] = pending
        await update.effective_chat.send_message(
            "❌ *PINs do not match.* Please try again.\n\nRe-enter your new passcode to confirm:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
        return
    db_set_pin(uid, hash_pin(pending))
    session_kill(uid)
    audit(uid, "reset_new_pin_set")
    log.info("New PIN set after reset uid=%s", uid)
    await update.effective_chat.send_message(
        "🎉 *New Passcode Set Successfully!*\n\n"
        "Your vault is now locked. Please unlock it with your new passcode.\n\n"
        "_Keep it safe — store it somewhere you won't forget._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_unlock(),
    )


# ─────────────────────────────────────────────────────────────
# 22.  STATS
# ─────────────────────────────────────────────────────────────
async def _do_stats(update: Update, uid: int) -> None:
    # BUG FIX: single aggregation pipeline instead of N+1 queries
    pipeline = [
        {"$match": {"uid": uid}},
        {"$group": {
            "_id":    None,
            "total":  {"$sum": 1},
            "oldest": {"$min": "$created"},
            "newest": {"$max": "$created"},
        }},
    ]
    agg = list(col_accounts.aggregate(pipeline))
    total = oldest = newest = None
    if agg:
        total  = agg[0]["total"]
        oldest = agg[0]["oldest"].strftime("%Y-%m-%d") if agg[0]["oldest"] else "—"
        newest = agg[0]["newest"].strftime("%Y-%m-%d") if agg[0]["newest"] else "—"
    else:
        total = 0

    algo_pipe = [
        {"$match": {"uid": uid}},
        {"$group": {"_id": "$algorithm", "count": {"$sum": 1}}},
    ]
    algo_rows = list(col_accounts.aggregate(algo_pipe))
    algo_lines = ""
    for r in sorted(algo_rows, key=lambda x: x["_id"]):
        algo_lines += f"\n  └ {r['_id']}: {r['count']}"

    user_doc    = col_users.find_one({"uid": uid}, {"joined": 1, "last_unlock": 1}) or {}
    joined      = user_doc.get("joined")
    last_unlock = user_doc.get("last_unlock")
    joined_s    = joined.strftime("%Y-%m-%d") if joined else "Unknown"
    unlock_s    = _human_age(last_unlock) if last_unlock else "Never"
    pin_set     = bool(db_get_pin(uid))
    paranoid    = db_get_setting(uid, "paranoid", False)

    starred_count = col_accounts.count_documents({"uid": uid, "starred": True})

    await update.message.reply_text(
        f"📊 *Your Stats*\n━━━━━━━━━━━━━━━━\n"
        f"🔐 Total accounts : `{total}`{algo_lines}\n"
        f"⭐ Starred        : `{starred_count}`\n"
        f"📅 Joined         : `{joined_s}`\n"
        f"🗓 Oldest account : `{oldest or '—'}`\n"
        f"🆕 Newest account : `{newest or '—'}`\n"
        f"🔑 Passcode       : {'✅ Set' if pin_set else '❌ Not set'}\n"
        f"🔕 Paranoid mode  : {'✅ ON' if paranoid else '❌ OFF'}\n"
        f"🕐 Last unlock    : `{unlock_s}`\n"
        f"⏱ Session TTL    : `{SESSION_TTL}s`",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_back_settings(),
    )
# ─────────────────────────────────────────────────────────────
async def watchdog(ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Periodic cleanup pass.
    Auto-lock notifications are now fired per-user by _auto_lock_user() tasks
    so the watchdog is only responsible for cleaning up stale DB rows and
    in-memory dicts that might have been missed (e.g. after a restart).
    """
    cutoff = datetime.now(timezone.utc) - timedelta(seconds=SESSION_TTL)
    try:
        # Remove any sessions that expired and whose auto-lock task never ran
        # (e.g. bot was restarted mid-session)
        expired_docs = list(col_sessions.find({"last": {"$lt": cutoff}}, {"uid": 1}))
        if expired_docs:
            r = col_sessions.delete_many({"last": {"$lt": cutoff}})
            log.info("Watchdog: cleaned %d stale session(s)", r.deleted_count)
            for doc in expired_docs:
                uid = doc.get("uid")
                if not uid:
                    continue
                _session_cache.pop(uid, None)
                # Cancel any lingering auto-lock task for this uid
                task = _auto_lock_tasks.pop(uid, None)
                if task and not task.done():
                    task.cancel()
                # Send lock notification only if no task already handled it
                pin_hash = db_get_pin(uid)
                if not pin_hash:
                    continue
                try:
                    await ctx.bot.send_message(
                        chat_id=uid,
                        text=(
                            "🔒 *Vault Auto-Locked*\n\n"
                            f"Your session expired after *{SESSION_TTL // 60} min* of inactivity.\n\n"
                            "Tap *🔓 Unlock Vault* to re-enter your passcode."
                        ),
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=rkb_unlock(),
                    )
                except TelegramError as te:
                    log.warning("Watchdog: could not notify uid=%s — %s", uid, te)
    except Exception as e:
        log.warning("Watchdog error: %s", e)

    # ── Memory housekeeping ──────────────────────────────────
    if len(_pending_updates) > 500:
        for k in list(_pending_updates.keys())[:250]:
            _pending_updates.pop(k, None)
    if len(_pending_qr) > 100:
        for k in list(_pending_qr.keys())[:50]:
            _pending_qr.pop(k, None)
    for uid_key in list(_bulk_refresh_tasks.keys()):
        _bulk_refresh_tasks[uid_key] = [t for t in _bulk_refresh_tasks[uid_key] if not t.done()]
        if not _bulk_refresh_tasks[uid_key]:
            _bulk_refresh_tasks.pop(uid_key, None)
    for req_id in list(_reset_reminder_tasks.keys()):
        if _reset_reminder_tasks[req_id].done():
            _reset_reminder_tasks.pop(req_id, None)
            _reset_admin_msg_ids.pop(req_id, None)
    # Clean up finished auto-lock tasks
    for uid_key in list(_auto_lock_tasks.keys()):
        if _auto_lock_tasks[uid_key].done():
            _auto_lock_tasks.pop(uid_key, None)


# ─────────────────────────────────────────────────────────────
# 24.  ERROR HANDLER
# ─────────────────────────────────────────────────────────────
async def on_error(update: object, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    log.exception("Unhandled error: %s", ctx.error)
    if isinstance(update, Update) and update.effective_message:
        try:
            await update.effective_message.reply_text(
                "⚠️ Something went wrong. Please try again or type /start.",
                reply_markup=rkb_home(),
            )
        except TelegramError:
            pass


# ─────────────────────────────────────────────────────────────
# 23.  ADMIN PANEL
# ─────────────────────────────────────────────────────────────

# ── Admin guard decorator ────────────────────────────────────
def admin_only(func):
    """Decorator: reject non-admin callers immediately."""
    async def wrapper(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        if update.effective_user.id != ADMIN_ID:
            await update.effective_message.reply_text("⛔ Admin only.")
            return
        return await func(update, ctx)
    wrapper.__name__ = func.__name__
    return wrapper


# ── Admin reply keyboard ─────────────────────────────────────
def rkb_admin() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("👥 Users"),          KeyboardButton("📊 Global Stats")],
            [KeyboardButton("📋 Audit Log"),       KeyboardButton("🔔 Pending Resets")],
            [KeyboardButton("📢 Broadcast"),       KeyboardButton("🔍 User Lookup")],
            [KeyboardButton("🚫 Ban User"),        KeyboardButton("✅ Unban User")],
            [KeyboardButton("🗑 Delete User"),     KeyboardButton("💬 Message User")],
            [KeyboardButton("🔒 Force Lock User"), KeyboardButton("📤 Export All Logs")],
            [KeyboardButton("👤 Login as User"),   KeyboardButton("⚙️ Bot Config")],
            [KeyboardButton("🏠 Home")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_admin_back() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("🔙 Admin Panel")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_admin_cancel() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("❌ Cancel"), KeyboardButton("🔙 Admin Panel")]],
        resize_keyboard=True,
        is_persistent=True,
    )


# ── Admin DB helpers ─────────────────────────────────────────
def db_ban_user(uid: int) -> None:
    col_users.update_one({"uid": uid}, {"$set": {"banned": True, "banned_at": datetime.now(timezone.utc)}})


def db_unban_user(uid: int) -> None:
    col_users.update_one({"uid": uid}, {"$set": {"banned": False, "banned_at": None}})


def db_is_banned(uid: int) -> bool:
    doc = col_users.find_one({"uid": uid}, {"banned": 1})
    return bool((doc or {}).get("banned", False))


def db_delete_user_all(uid: int) -> dict:
    """Wipe all data for a user. Returns counts."""
    accts    = col_accounts.delete_many({"uid": uid}).deleted_count
    sessions = col_sessions.delete_many({"uid": uid}).deleted_count
    users    = col_users.delete_many({"uid": uid}).deleted_count
    col_reset_requests.delete_many({"uid": uid})
    _session_cache.pop(uid, None)
    _invalidate_cache(uid)
    return {"accounts": accts, "sessions": sessions, "users": users}


def db_get_all_users(page: int = 0, page_size: int = 10) -> list:
    return list(col_users.find(
        {},
        {"uid": 1, "name": 1, "username": 1, "joined": 1, "last_seen": 1,
         "banned": 1, "last_unlock": 1},
    ).sort("joined", -1).skip(page * page_size).limit(page_size))


def db_count_users() -> int:
    return col_users.count_documents({})


def db_find_user(query: str) -> Optional[dict]:
    """Find a user by UID (int string) or @username."""
    if query.lstrip("-").isdigit():
        return col_users.find_one({"uid": int(query)})
    uname = query.lstrip("@")
    return col_users.find_one({"username": {"$regex": f"^{re.escape(uname)}$", "$options": "i"}})


def db_get_recent_audit(limit: int = 20, uid_filter: Optional[int] = None) -> list:
    filt = {"uid": uid_filter} if uid_filter else {}
    return list(col_audit.find(filt, {"_id": 0}).sort("ts", -1).limit(limit))


def db_global_stats() -> dict:
    total_users    = col_users.count_documents({})
    banned_users   = col_users.count_documents({"banned": True})
    total_accounts = col_accounts.count_documents({})
    active_sessions = col_sessions.count_documents({})
    pending_resets = col_reset_requests.count_documents({"status": "pending"})
    now = datetime.now(timezone.utc)
    new_users_24h = col_users.count_documents({"joined": {"$gte": now - timedelta(hours=24)}})
    audit_24h     = col_audit.count_documents({"ts": {"$gte": now - timedelta(hours=24)}})
    audit_7d      = col_audit.count_documents({"ts": {"$gte": now - timedelta(days=7)}})
    # Top action breakdown from last 7 days
    pipe = [
        {"$match": {"ts": {"$gte": now - timedelta(days=7)}}},
        {"$group": {"_id": "$action", "count": {"$sum": 1}}},
        {"$sort": {"count": -1}},
        {"$limit": 8},
    ]
    action_rows = list(col_audit.aggregate(pipe))
    return {
        "total_users": total_users,
        "banned_users": banned_users,
        "total_accounts": total_accounts,
        "active_sessions": active_sessions,
        "pending_resets": pending_resets,
        "new_users_24h": new_users_24h,
        "audit_24h": audit_24h,
        "audit_7d": audit_7d,
        "action_rows": action_rows,
    }


def db_mongo_storage_info() -> dict:
    """
    Query MongoDB dbStats for storage usage.
    Returns human-readable strings and raw values.
    Works on Atlas free/shared tiers (M0/M2/M5) which expose freeStorageSize,
    and on self-hosted instances via standard dbStats fields.
    """
    def _fmt(b: int) -> str:
        if b >= 1_073_741_824:
            return f"{b / 1_073_741_824:.2f} GB"
        if b >= 1_048_576:
            return f"{b / 1_048_576:.2f} MB"
        return f"{b // 1024} KB"

    try:
        s = _db.command("dbStats", 1024)   # scale=1024 → values in KB
        # dbStats returns KB when scale=1024; convert back to bytes for _fmt
        data_bytes     = int(s.get("dataSize",        0)) * 1024
        storage_bytes  = int(s.get("storageSize",     0)) * 1024
        index_bytes    = int(s.get("indexSize",       0)) * 1024
        fs_used_bytes  = int(s.get("fsUsedSize",      0)) * 1024
        fs_total_bytes = int(s.get("fsTotalSize",     0)) * 1024
        free_bytes     = int(s.get("freeStorageSize", 0)) * 1024  # Atlas-specific

        # Derive free space: prefer Atlas freeStorageSize, else filesystem level
        pct_used = None
        bar      = ""
        if free_bytes:
            free_str = _fmt(free_bytes)
        elif fs_total_bytes:
            free_bytes = fs_total_bytes - fs_used_bytes
            free_str   = _fmt(free_bytes)
            pct_used   = fs_used_bytes / fs_total_bytes * 100
        else:
            free_str = "_unavailable_"

        if pct_used is not None:
            filled = int(pct_used / 10)
            bar    = "█" * filled + "░" * (10 - filled)

        return {
            "ok":          True,
            "data":        _fmt(data_bytes),
            "storage":     _fmt(storage_bytes),
            "indexes":     _fmt(index_bytes),
            "free":        free_str,
            "pct_used":    f"{pct_used:.1f}%" if pct_used is not None else None,
            "bar":         bar,
            "collections": int(s.get("collections", 0)),
            "objects":     int(s.get("objects",     0)),
        }
    except Exception as exc:
        log.warning("db_mongo_storage_info failed: %s", exc)
        return {"ok": False, "error": str(exc)}


# ── Inline keyboards for admin ───────────────────────────────
def ikb_admin_user_actions(target_uid: int, banned: bool) -> InlineKeyboardMarkup:
    ban_label  = "✅ Unban" if banned else "🚫 Ban"
    ban_cb     = f"ADMIN_UNBAN:{target_uid}" if banned else f"ADMIN_BAN:{target_uid}"
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(ban_label,            callback_data=ban_cb),
            InlineKeyboardButton("🗑 Delete All Data",  callback_data=f"ADMIN_DEL_USER:{target_uid}"),
        ],
        [
            InlineKeyboardButton("🔒 Force Lock",      callback_data=f"ADMIN_LOCK:{target_uid}"),
            InlineKeyboardButton("💬 Send Message",    callback_data=f"ADMIN_MSG:{target_uid}"),
        ],
        [
            InlineKeyboardButton("📋 Audit Trail",     callback_data=f"ADMIN_AUDIT:{target_uid}"),
            InlineKeyboardButton("📊 User Stats",      callback_data=f"ADMIN_USTATS:{target_uid}"),
        ],
        [
            InlineKeyboardButton("👤 Login as User",   callback_data=f"ADMIN_IMPERSONATE:{target_uid}"),
        ],
    ])


def ikb_admin_confirm_delete(target_uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("⚠️ YES — Delete Everything", callback_data=f"ADMIN_DEL_CONFIRM:{target_uid}"),
            InlineKeyboardButton("❌ Cancel",                   callback_data="ADMIN_CANCEL"),
        ]
    ])


def ikb_admin_users_page(page: int, total: int, page_size: int = 10) -> InlineKeyboardMarkup:
    rows = []
    nav  = []
    if page > 0:
        nav.append(InlineKeyboardButton("◀️ Prev", callback_data=f"ADMIN_USERS_PAGE:{page-1}"))
    if (page + 1) * page_size < total:
        nav.append(InlineKeyboardButton("▶️ Next", callback_data=f"ADMIN_USERS_PAGE:{page+1}"))
    if nav:
        rows.append(nav)
    return InlineKeyboardMarkup(rows) if rows else None


# ── Admin command: /admin ─────────────────────────────────────
@admin_only
async def cmd_admin(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data.clear()
    ctx.user_data["admin_mode"] = True
    stats = db_global_stats()
    await update.message.reply_text(
        "🛡 *NexAuth Admin Panel*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Users        : `{stats['total_users']}`  _(+{stats['new_users_24h']} today)_\n"
        f"🔐 Accounts     : `{stats['total_accounts']}`\n"
        f"🔓 Sessions     : `{stats['active_sessions']}`\n"
        f"🚫 Banned       : `{stats['banned_users']}`\n"
        f"🔔 Pending resets: `{stats['pending_resets']}`\n"
        f"📋 Actions 24h  : `{stats['audit_24h']}`\n\n"
        "Use the panel below to manage the bot.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin(),
    )


# ── Admin: global stats ──────────────────────────────────────
@admin_only
async def _admin_global_stats(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    s = db_global_stats()
    action_lines = "\n".join(
        f"  `{r['_id']}` — {r['count']}" for r in s["action_rows"]
    ) or "  _(none)_"
    await update.effective_chat.send_message(
        "📊 *Global Bot Statistics*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Total users       : `{s['total_users']}`\n"
        f"  └ New (24h)        : `{s['new_users_24h']}`\n"
        f"  └ Banned           : `{s['banned_users']}`\n"
        f"🔐 Total accounts    : `{s['total_accounts']}`\n"
        f"🔓 Active sessions   : `{s['active_sessions']}`\n"
        f"🔔 Pending resets    : `{s['pending_resets']}`\n"
        f"📋 Audit events 24h  : `{s['audit_24h']}`\n"
        f"📋 Audit events 7d   : `{s['audit_7d']}`\n\n"
        f"*Top actions (7d):*\n{action_lines}",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Admin: list users ────────────────────────────────────────
async def _admin_list_users(update_or_q, ctx, page: int = 0) -> None:
    page_size = 10
    total     = db_count_users()
    users     = db_get_all_users(page, page_size)
    if not users:
        text = "👥 *No users registered.*"
        markup = rkb_admin_back()
    else:
        lines = []
        for u in users:
            j     = u.get("joined")
            j_str = j.strftime("%m-%d") if j else "?"
            ban   = " 🚫" if u.get("banned") else ""
            uname = f"@{u['username']}" if u.get("username") else "—"
            lines.append(f"`{u['uid']}`  {u.get('name','?')[:16]}  {uname}  _{j_str}_{ban}")
        start = page * page_size + 1
        end   = min(start + page_size - 1, total)
        text  = (
            f"👥 *Users {start}–{end} of {total}*\n"
            "━━━━━━━━━━━━━━━━━━━━━━━━\n"
            + "\n".join(lines)
        )
        markup = ikb_admin_users_page(page, total, page_size)

    if hasattr(update_or_q, "edit_message_text"):
        try:
            await update_or_q.edit_message_text(text, parse_mode=ParseMode.MARKDOWN, reply_markup=markup)
        except Exception:
            pass
    else:
        await update_or_q.effective_chat.send_message(
            text, parse_mode=ParseMode.MARKDOWN,
            reply_markup=markup or rkb_admin_back(),
        )


# ── Admin: audit log ────────────────────────────────────────
@admin_only
async def _admin_audit_log(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                            uid_filter: Optional[int] = None) -> None:
    rows = db_get_recent_audit(limit=25, uid_filter=uid_filter)
    if not rows:
        await update.effective_chat.send_message(
            "📋 *Audit log is empty.*",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return
    lines = []
    for r in rows:
        ts     = r["ts"].strftime("%m-%d %H:%M") if r.get("ts") else "?"
        action = r.get("action", "?")
        detail = f" `{r['detail']}`" if r.get("detail") else ""
        uid_s  = f"`{r['uid']}`" if uid_filter is None else ""
        lines.append(f"`{ts}` {uid_s} *{action}*{detail}")
    header = f"📋 *Audit Log* {'for user `'+str(uid_filter)+'`' if uid_filter else '(global, last 25)'}"
    await update.effective_chat.send_message(
        header + "\n━━━━━━━━━━━━━━━━━━━━━━━━\n" + "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Admin: pending resets ────────────────────────────────────
@admin_only
async def _admin_pending_resets(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    reqs = list(col_reset_requests.find(
        {"status": "pending"},
        {"request_id": 1, "uid": 1, "name": 1, "username": 1, "ts": 1, "_id": 0},
    ).sort("ts", -1).limit(20))
    if not reqs:
        await update.effective_chat.send_message(
            "🔔 *No pending reset requests.*",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return
    lines = []
    for r in reqs:
        ts    = r["ts"].strftime("%m-%d %H:%M") if r.get("ts") else "?"
        uname = f"@{r['username']}" if r.get("username") else "—"
        lines.append(
            f"`{ts}` — {r.get('name','?')} {uname} `{r['uid']}`\n"
            f"  ↳ /resetreview_{r['request_id'][:8]}"
        )
    await update.effective_chat.send_message(
        f"🔔 *Pending Reset Requests* ({len(reqs)})\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        + "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Admin: user lookup ───────────────────────────────────────
@admin_only
async def _admin_user_lookup(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                              query: str) -> None:
    doc = db_find_user(query)
    if not doc:
        await update.effective_chat.send_message(
            f"❌ *User not found:* `{query}`",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return
    target_uid = doc["uid"]
    acct_count = col_accounts.count_documents({"uid": target_uid})
    joined     = doc.get("joined")
    last_seen  = doc.get("last_seen")
    last_unlock = doc.get("last_unlock")
    banned     = bool(doc.get("banned"))
    has_pin    = bool(db_get_pin(target_uid))
    has_secq   = db_has_security_answers(target_uid)
    active     = session_alive(target_uid)
    uname      = f"@{doc['username']}" if doc.get("username") else "—"
    await update.effective_chat.send_message(
        f"👤 *User Profile*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 UID         : `{target_uid}`\n"
        f"👤 Name        : {doc.get('name','?')}\n"
        f"🔗 Username    : {uname}\n"
        f"📅 Joined      : `{joined.strftime('%Y-%m-%d') if joined else '?'}`\n"
        f"👁 Last seen   : `{_human_age(last_seen) if last_seen else '?'}`\n"
        f"🔓 Last unlock : `{_human_age(last_unlock) if last_unlock else 'Never'}`\n"
        f"🔐 Accounts    : `{acct_count}`\n"
        f"🔑 Passcode    : {'✅ Set' if has_pin else '❌ Not set'}\n"
        f"🛡 Security Q  : {'✅ Set' if has_secq else '❌ Not set'}\n"
        f"📡 Session     : {'🟢 Active' if active else '⚫ Inactive'}\n"
        f"🚫 Banned      : {'⚠️ YES' if banned else '✅ No'}",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_admin_user_actions(target_uid, banned),
    )


# ── Admin: ban / unban ───────────────────────────────────────
async def _admin_do_ban(q, target_uid: int) -> None:
    db_ban_user(target_uid)
    session_kill(target_uid)
    audit(target_uid, "admin_ban", str(ADMIN_ID))
    log.info("Admin banned uid=%s", target_uid)
    doc     = col_users.find_one({"uid": target_uid}) or {}
    banned  = True
    await q.edit_message_reply_markup(reply_markup=ikb_admin_user_actions(target_uid, banned))
    await q.message.reply_text(
        f"🚫 *User `{target_uid}` has been banned.*\nTheir session was killed.",
        parse_mode=ParseMode.MARKDOWN,
    )
    # Notify the user
    try:
        await q.bot.send_message(
            chat_id=target_uid,
            text="🚫 *Your account has been suspended.*\nPlease contact the admin.",
            parse_mode=ParseMode.MARKDOWN,
        )
    except TelegramError:
        pass


async def _admin_do_unban(q, target_uid: int) -> None:
    db_unban_user(target_uid)
    audit(target_uid, "admin_unban", str(ADMIN_ID))
    log.info("Admin unbanned uid=%s", target_uid)
    await q.edit_message_reply_markup(reply_markup=ikb_admin_user_actions(target_uid, False))
    await q.message.reply_text(
        f"✅ *User `{target_uid}` has been unbanned.*",
        parse_mode=ParseMode.MARKDOWN,
    )
    try:
        await q.bot.send_message(
            chat_id=target_uid,
            text="✅ *Your account has been reinstated.*\nYou can use NexAuth again.",
            parse_mode=ParseMode.MARKDOWN,
        )
    except TelegramError:
        pass


# ── Admin: force lock user ───────────────────────────────────
async def _admin_force_lock(q, target_uid: int) -> None:
    session_kill(target_uid)
    audit(target_uid, "admin_force_lock", str(ADMIN_ID))
    log.info("Admin force-locked uid=%s", target_uid)
    await q.message.reply_text(
        f"🔒 *User `{target_uid}` session force-locked.*",
        parse_mode=ParseMode.MARKDOWN,
    )
    try:
        await q.bot.send_message(
            chat_id=target_uid,
            text="🔒 *Your vault has been locked by the admin.*",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )
    except TelegramError:
        pass


# ── Admin: per-user stats (from inline button) ───────────────
async def _admin_user_stats(q, target_uid: int) -> None:
    acct_count = col_accounts.count_documents({"uid": target_uid})
    starred    = col_accounts.count_documents({"uid": target_uid, "starred": True})
    has_pin    = bool(db_get_pin(target_uid))
    doc        = col_users.find_one({"uid": target_uid}) or {}
    joined     = doc.get("joined")
    last_unlock = doc.get("last_unlock")
    audit_count = col_audit.count_documents({"uid": target_uid})
    pending_reset = db_get_reset_request_by_uid(target_uid)
    await q.message.reply_text(
        f"📊 *User Stats — `{target_uid}`*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔐 Accounts     : `{acct_count}`\n"
        f"⭐ Starred      : `{starred}`\n"
        f"🔑 Passcode     : {'✅ Set' if has_pin else '❌ Not set'}\n"
        f"📋 Audit events : `{audit_count}`\n"
        f"📅 Joined       : `{joined.strftime('%Y-%m-%d') if joined else '?'}`\n"
        f"🔓 Last unlock  : `{_human_age(last_unlock) if last_unlock else 'Never'}`\n"
        f"🔔 Pending reset: {'⚠️ Yes' if pending_reset else '✅ No'}",
        parse_mode=ParseMode.MARKDOWN,
    )


# ── Admin: send message to user ──────────────────────────────
async def _admin_do_send_message(q, ctx, target_uid: int, text: str) -> None:
    try:
        await q.bot.send_message(
            chat_id=target_uid,
            text=f"📩 *Message from Admin*\n\n{text}",
            parse_mode=ParseMode.MARKDOWN,
        )
        audit(target_uid, "admin_message", text[:64])
        await ctx.bot.send_message(
            chat_id=ADMIN_ID,
            text=f"✅ Message delivered to `{target_uid}`.",
            parse_mode=ParseMode.MARKDOWN,
        )
    except TelegramError as e:
        await ctx.bot.send_message(
            chat_id=ADMIN_ID,
            text=f"❌ Could not deliver to `{target_uid}`: {e}",
            parse_mode=ParseMode.MARKDOWN,
        )


# ── Admin: export audit log as text file ─────────────────────
@admin_only
async def _admin_export_logs(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    rows = list(col_audit.find({}, {"_id": 0}).sort("ts", -1).limit(500))
    if not rows:
        await update.effective_chat.send_message(
            "📋 Audit log is empty.", reply_markup=rkb_admin_back()
        )
        return
    lines = []
    for r in rows:
        ts     = r["ts"].strftime("%Y-%m-%d %H:%M:%S UTC") if r.get("ts") else "?"
        lines.append(f"{ts}  uid={r.get('uid','?')}  action={r.get('action','?')}  detail={r.get('detail','')}")
    content = "\n".join(lines).encode()
    bio     = io.BytesIO(content)
    bio.name = f"nexauth_audit_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M')}.txt"
    await update.effective_chat.send_document(
        document=bio,
        caption="📤 *Audit log export* (last 500 entries)",
        parse_mode=ParseMode.MARKDOWN,
    )
    audit(ADMIN_ID, "admin_export_logs")


# ── Admin: bot config view ────────────────────────────────────
@admin_only
async def _admin_bot_config(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    await update.effective_chat.send_message(
        "⚙️ *Bot Configuration*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"⏱ Session TTL     : `{SESSION_TTL}s` ({SESSION_TTL//60}min)\n"
        f"🔒 PIN lockout     : `{PIN_LOCKOUT_S}s` ({PIN_LOCKOUT_S//60}min)\n"
        f"📤 Export TTL      : `{EXPORT_TTL_S}s`\n"
        f"💾 Backup TTL      : `{BACKUP_TTL_S}s`\n"
        f"🔕 Paranoid TTL    : `{PARANOID_TTL_S}s`\n"
        f"📄 Page size       : `{PAGE_SIZE}`\n"
        f"🔑 Admin UID       : `{ADMIN_ID}`\n"
        f"🛡 Security Qs     : `{len(SECURITY_QUESTIONS)}`\n\n"
        "_These values are set via environment variables and .env file._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Admin: broadcast (interactive, from admin panel) ─────────
@admin_only
async def _admin_start_broadcast(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_BROADCAST"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "📢 *Broadcast*\n\nSend the message text you want to broadcast to all users.\n"
        "_Supports Markdown formatting._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start user-lookup flow ────────────────────────────
@admin_only
async def _admin_start_lookup(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_LOOKUP"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🔍 *User Lookup*\n\nSend a user ID (number) or @username.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start ban flow ─────────────────────────────────────
@admin_only
async def _admin_start_ban(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_BAN"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🚫 *Ban User*\n\nSend the user ID or @username to ban.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start unban flow ───────────────────────────────────
@admin_only
async def _admin_start_unban(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_UNBAN"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "✅ *Unban User*\n\nSend the user ID or @username to unban.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start delete-user flow ────────────────────────────
@admin_only
async def _admin_start_delete_user(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_DELETE_USER"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🗑 *Delete User*\n\n⚠️ This wipes ALL data for a user permanently.\n\n"
        "Send the user ID or @username.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start message-user flow ───────────────────────────
@admin_only
async def _admin_start_message_user(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_MSG_TARGET"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "💬 *Message User*\n\nSend the user ID or @username of the recipient.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin: start force-lock flow ─────────────────────────────
@admin_only
async def _admin_start_force_lock(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_FORCE_LOCK"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🔒 *Force Lock User*\n\nSend the user ID or @username to force-lock.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Admin /resetreview_<id> command ──────────────────────────
async def cmd_resetreview(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user.id != ADMIN_ID:
        await update.message.reply_text("⛔ Admin only.")
        return
    # Extract the partial request_id from the command text
    text    = update.message.text or ""
    partial = text.split("_", 1)[-1].strip()   # /resetreview_XXXXXXXX → XXXXXXXX
    if not partial:
        await update.message.reply_text("Usage: /resetreview_<request_id_prefix>")
        return
    req = col_reset_requests.find_one(
        {"request_id": {"$regex": f"^{re.escape(partial)}"}},
    )
    if not req:
        await update.message.reply_text(f"❌ Reset request not found: `{partial}`",
                                         parse_mode=ParseMode.MARKDOWN)
        return
    stored_plain = db_get_security_answers_plain(req["uid"]) or []
    qa_section   = ""
    if req.get("qa"):
        lines = []
        for i, item in enumerate(req["qa"]):
            stored_ans = stored_plain[i] if i < len(stored_plain) else "_(not stored)_"
            lines.append(
                f"*Q{i+1}:* {item['q']}\n"
                f"  📂 Stored : `{stored_ans}`\n"
                f"  ✏️ User   : `{item['a']}`"
            )
        qa_section = "\n\n🔍 *Q&A Comparison:*\n" + "\n\n".join(lines)
    else:
        qa_section = "\n\n⚠️ _No security questions set._"
    ts  = req["ts"].strftime("%Y-%m-%d %H:%M UTC") if req.get("ts") else "?"
    uname = f"@{req['username']}" if req.get("username") else "—"
    await update.message.reply_text(
        f"🔔 *Reset Request Review*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👤 Name     : {req.get('name','?')}\n"
        f"🔗 Username : {uname}\n"
        f"🆔 UID      : `{req['uid']}`\n"
        f"🕐 Time     : {ts}\n"
        f"📌 Status   : `{req.get('status','?')}`"
        + qa_section,
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_admin_reset(req["request_id"]),
    )


# ── Ban enforcement hook ─────────────────────────────────────
# Injected at the top of on_message so banned users get an immediate block.
async def _check_ban(update: Update) -> bool:
    """Returns True if the user is banned (caller should return early)."""
    uid = update.effective_user.id if update.effective_user else None
    if uid and uid != ADMIN_ID and db_is_banned(uid):
        try:
            await update.effective_chat.send_message(
                "🚫 *Your account has been suspended.*\nContact the admin for assistance."
                if not update.effective_chat.send_message else
                "🚫 Your account is suspended.",
                parse_mode=ParseMode.MARKDOWN,
            )
        except Exception:
            pass
        return True
    return False


# ── Admin message router (handles admin panel button presses) ─
async def _handle_admin_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                  uid: int, text: str, state: str) -> bool:
    """
    Called from on_message BEFORE the regular router.
    Returns True if the message was consumed by the admin flow.
    """
    if uid != ADMIN_ID:
        return False

    # ── Back to admin panel ──────────────────────────────────
    if text == "🔙 Admin Panel":
        ctx.user_data.clear()
        ctx.user_data["admin_mode"] = True
        stats = db_global_stats()
        await update.effective_chat.send_message(
            "🛡 *Admin Panel*\n"
            f"👥 `{stats['total_users']}` users · 🔐 `{stats['total_accounts']}` accounts · "
            f"🔔 `{stats['pending_resets']}` pending resets",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin(),
        )
        return True

    # ── Admin panel main buttons ─────────────────────────────
    if text == "👥 Users":
        await _admin_list_users(update, ctx, page=0)
        return True
    if text == "📊 Global Stats":
        await _admin_global_stats(update, ctx)
        return True
    if text == "📋 Audit Log":
        await _admin_audit_log(update, ctx)
        return True
    if text == "🔔 Pending Resets":
        await _admin_pending_resets(update, ctx)
        return True
    if text == "📢 Broadcast":
        await _admin_start_broadcast(update, ctx)
        return True
    if text == "🔍 User Lookup":
        await _admin_start_lookup(update, ctx)
        return True
    if text == "🚫 Ban User":
        await _admin_start_ban(update, ctx)
        return True
    if text == "✅ Unban User":
        await _admin_start_unban(update, ctx)
        return True
    if text == "🗑 Delete User":
        await _admin_start_delete_user(update, ctx)
        return True
    if text == "💬 Message User":
        await _admin_start_message_user(update, ctx)
        return True
    if text == "🔒 Force Lock User":
        await _admin_start_force_lock(update, ctx)
        return True
    if text == "📤 Export All Logs":
        await _admin_export_logs(update, ctx)
        return True
    if text == "⚙️ Bot Config":
        await _admin_bot_config(update, ctx)
        return True
    if text == "👤 Login as User":
        ctx.user_data["state"]      = "ADMIN_WAIT_IMPERSONATE"
        ctx.user_data["admin_mode"] = True
        await update.effective_chat.send_message(
            "👤 *Login as User*\n\n"
            "Send the user ID or @username of the user whose vault you want to access.\n\n"
            "⚠️ _All actions will be performed on their real vault and logged in the audit trail._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_cancel(),
        )
        return True
    # "🏠 Home" exits admin mode and goes to regular home
    if text == "🏠 Home" and ctx.user_data.get("admin_mode"):
        ctx.user_data.clear()
        # Fall through to regular home handler below
        return False

    # ── Admin wait-states ────────────────────────────────────
    if state == "ADMIN_WAIT_BROADCAST":
        if text in ("❌ Cancel", "🔙 Admin Panel"):
            return False  # let the Cancel/Back handler run
        # Run broadcast using existing cmd_broadcast logic
        users = list(col_users.find({}, {"uid": 1}))
        total = len(users)
        prog  = await update.effective_chat.send_message(
            f"📢 Broadcasting to {total} user(s)…",
            parse_mode=ParseMode.MARKDOWN,
        )
        sent = failed = blocked = 0
        for i, u in enumerate(users, 1):
            try:
                await ctx.bot.send_message(
                    u["uid"],
                    f"📢 *Announcement*\n\n{text}",
                    parse_mode=ParseMode.MARKDOWN,
                )
                sent += 1
            except TelegramError as e:
                err = str(e).lower()
                if any(x in err for x in ("blocked", "deactivated", "not found", "forbidden")):
                    blocked += 1
                else:
                    failed += 1
            await asyncio.sleep(0.05)
            if i % 25 == 0 or i == total:
                try:
                    await prog.edit_text(
                        f"📢 `{i}/{total}` — ✅{sent} 🚫{blocked} ❌{failed}",
                        parse_mode=ParseMode.MARKDOWN,
                    )
                except TelegramError:
                    pass
        ctx.user_data.pop("state", None)
        try:
            await prog.edit_text(
                f"✅ *Broadcast done*\n• Sent: `{sent}`\n• Blocked: `{blocked}`\n• Errors: `{failed}`",
                parse_mode=ParseMode.MARKDOWN,
            )
        except TelegramError:
            pass
        audit(ADMIN_ID, "admin_broadcast", f"sent={sent}")
        await update.effective_chat.send_message("Back to panel.", reply_markup=rkb_admin())
        return True

    if state == "ADMIN_WAIT_LOOKUP":
        ctx.user_data.pop("state", None)
        await _admin_user_lookup(update, ctx, text.strip())
        return True

    if state == "ADMIN_WAIT_BAN":
        ctx.user_data.pop("state", None)
        doc = db_find_user(text.strip())
        if not doc:
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        else:
            db_ban_user(doc["uid"])
            session_kill(doc["uid"])
            audit(doc["uid"], "admin_ban", str(ADMIN_ID))
            await update.effective_chat.send_message(
                f"🚫 *User `{doc['uid']}` banned and session killed.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
            try:
                await ctx.bot.send_message(
                    doc["uid"],
                    "🚫 *Your account has been suspended.*\nContact the admin.",
                    parse_mode=ParseMode.MARKDOWN,
                )
            except TelegramError:
                pass
        return True

    if state == "ADMIN_WAIT_UNBAN":
        ctx.user_data.pop("state", None)
        doc = db_find_user(text.strip())
        if not doc:
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        else:
            db_unban_user(doc["uid"])
            audit(doc["uid"], "admin_unban", str(ADMIN_ID))
            await update.effective_chat.send_message(
                f"✅ *User `{doc['uid']}` unbanned.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
            try:
                await ctx.bot.send_message(
                    doc["uid"],
                    "✅ *Your account has been reinstated.*",
                    parse_mode=ParseMode.MARKDOWN,
                )
            except TelegramError:
                pass
        return True

    if state == "ADMIN_WAIT_DELETE_USER":
        ctx.user_data.pop("state", None)
        doc = db_find_user(text.strip())
        if not doc:
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        else:
            target_uid = doc["uid"]
            ctx.user_data["admin_delete_uid"] = target_uid
            ctx.user_data["state"] = "ADMIN_WAIT_DELETE_CONFIRM"
            await update.effective_chat.send_message(
                f"⚠️ *Confirm Delete*\n\n"
                f"This will permanently wipe *all data* for:\n"
                f"👤 `{target_uid}` — {doc.get('name','?')}\n\n"
                f"Are you absolutely sure?",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=ikb_admin_confirm_delete(target_uid),
            )
        return True

    if state == "ADMIN_WAIT_MSG_TARGET":
        doc = db_find_user(text.strip())
        if not doc:
            ctx.user_data.pop("state", None)
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        else:
            ctx.user_data["admin_msg_target"] = doc["uid"]
            ctx.user_data["state"] = "ADMIN_WAIT_MSG_TEXT"
            await update.effective_chat.send_message(
                f"💬 *Message to `{doc['uid']}`*\n\nNow send the message text.",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_admin_cancel(),
            )
        return True

    if state == "ADMIN_WAIT_MSG_TEXT":
        target_uid = ctx.user_data.pop("admin_msg_target", None)
        ctx.user_data.pop("state", None)
        if not target_uid:
            await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_admin())
            return True
        try:
            await ctx.bot.send_message(
                chat_id=target_uid,
                text=f"📩 *Message from Admin*\n\n{text}",
                parse_mode=ParseMode.MARKDOWN,
            )
            audit(target_uid, "admin_message", text[:64])
            await update.effective_chat.send_message(
                f"✅ Message delivered to `{target_uid}`.",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        except TelegramError as e:
            await update.effective_chat.send_message(
                f"❌ Delivery failed: {e}", reply_markup=rkb_admin_back()
            )
        return True

    if state == "ADMIN_WAIT_FORCE_LOCK":
        ctx.user_data.pop("state", None)
        doc = db_find_user(text.strip())
        if not doc:
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
        else:
            target_uid = doc["uid"]
            session_kill(target_uid)
            audit(target_uid, "admin_force_lock", str(ADMIN_ID))
            await update.effective_chat.send_message(
                f"🔒 *User `{target_uid}` session killed.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
            )
            try:
                await ctx.bot.send_message(
                    target_uid,
                    "🔒 *Your vault has been locked by the admin.*",
                    parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_unlock(),
                )
            except TelegramError:
                pass
        return True

    if state == "ADMIN_WAIT_IMPERSONATE":
        doc = db_find_user(text.strip())
        if not doc:
            await update.effective_chat.send_message(
                f"❌ User not found: `{text.strip()}`\n\nSend a numeric user ID or @username.",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_cancel(),
            )
            # Keep state so admin can retry without re-pressing the button
        else:
            ctx.user_data.pop("state", None)
            target_uid = doc["uid"]
            if target_uid == ADMIN_ID:
                await update.effective_chat.send_message(
                    "⚠️ Cannot impersonate yourself.",
                    reply_markup=rkb_admin_back(),
                )
            else:
                await _admin_enter_user(update, ctx, uid, target_uid)
        return True

    return False


# ── Admin inline callback router (injected into on_button) ────
async def _handle_admin_callback(q, ctx, uid: int, data: str) -> bool:
    """
    Called from on_button BEFORE the main router.
    Returns True if consumed.
    """
    if uid != ADMIN_ID:
        return False

    if data.startswith("ADMIN_IMPERSONATE:"):
        target_uid = int(data.split(":", 1)[1])
        if target_uid == ADMIN_ID:
            await q.answer("Cannot impersonate yourself.", show_alert=True)
        else:
            # FIX BUG 3: removed duplicate q.answer() — on_button already calls it
            # unconditionally at the top. Calling it twice raises "query already answered".
            await _admin_enter_user(q.message, ctx, uid, target_uid)
        return True

    if data.startswith("ADMIN_BAN:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_do_ban(q, target_uid)
        return True

    if data.startswith("ADMIN_UNBAN:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_do_unban(q, target_uid)
        return True

    if data.startswith("ADMIN_LOCK:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_force_lock(q, target_uid)
        return True

    if data.startswith("ADMIN_MSG:"):
        target_uid = int(data.split(":", 1)[1])
        ctx.user_data["admin_msg_target"] = target_uid
        ctx.user_data["state"]            = "ADMIN_WAIT_MSG_TEXT"
        ctx.user_data["admin_mode"]       = True
        await q.message.reply_text(
            f"💬 *Message to `{target_uid}`*\n\nSend the message text now.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_cancel(),
        )
        return True

    if data.startswith("ADMIN_AUDIT:"):
        target_uid = int(data.split(":", 1)[1])
        rows = db_get_recent_audit(limit=15, uid_filter=target_uid)
        if not rows:
            await q.message.reply_text("📋 No audit entries for this user.")
            return True
        lines = [
            f"`{r['ts'].strftime('%m-%d %H:%M')}` *{r.get('action','?')}*"
            + (f" `{r['detail']}`" if r.get("detail") else "")
            for r in rows
        ]
        await q.message.reply_text(
            f"📋 *Audit trail for `{target_uid}`* (last 15)\n━━━━━━━━━━━━━━━━━━━━━━━━\n"
            + "\n".join(lines),
            parse_mode=ParseMode.MARKDOWN,
        )
        return True

    if data.startswith("ADMIN_USTATS:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_user_stats(q, target_uid)
        return True

    if data.startswith("ADMIN_DEL_USER:"):
        target_uid = int(data.split(":", 1)[1])
        doc = col_users.find_one({"uid": target_uid}) or {}
        await q.edit_message_reply_markup(reply_markup=ikb_admin_confirm_delete(target_uid))
        await q.message.reply_text(
            f"⚠️ *Confirm: permanently delete all data for `{target_uid}`* ({doc.get('name','?')})?",
            parse_mode=ParseMode.MARKDOWN,
        )
        return True

    if data.startswith("ADMIN_DEL_CONFIRM:"):
        target_uid = int(data.split(":", 1)[1])
        result = db_delete_user_all(target_uid)
        session_kill(target_uid)
        audit(ADMIN_ID, "admin_delete_user", str(target_uid))
        log.info("Admin deleted uid=%s data=%s", target_uid, result)
        await q.edit_message_text(
            f"🗑 *User `{target_uid}` fully deleted.*\n"
            f"• Accounts: `{result['accounts']}`\n"
            f"• Sessions: `{result['sessions']}`\n"
            f"• User doc: `{result['users']}`",
            parse_mode=ParseMode.MARKDOWN,
        )
        try:
            await ctx.bot.send_message(
                chat_id=target_uid,
                text="🗑 Your account and all data have been removed by the admin.",
            )
        except TelegramError:
            pass
        return True

    if data == "ADMIN_CANCEL":
        try:
            await q.edit_message_reply_markup(reply_markup=None)
        except (BadRequest, TelegramError):
            pass
        return True

    if data.startswith("ADMIN_USERS_PAGE:"):
        page = int(data.split(":", 1)[1])
        await _admin_list_users(q, ctx, page=page)
        return True

    return False


# ─────────────────────────────────────────────────────────────
# 24.  ADMIN IMPERSONATION ("Login as User")
# ─────────────────────────────────────────────────────────────

def impersonate_start(admin_uid: int, target_uid: int) -> None:
    """Begin impersonating target_uid as admin_uid."""
    _impersonation[admin_uid] = target_uid
    audit(admin_uid, "admin_impersonate_start", str(target_uid))
    log.info("Admin uid=%s started impersonating uid=%s", admin_uid, target_uid)


def impersonate_end(admin_uid: int) -> Optional[int]:
    """End impersonation. Returns the target uid that was being impersonated, or None."""
    target = _impersonation.pop(admin_uid, None)
    if target:
        audit(admin_uid, "admin_impersonate_end", str(target))
        log.info("Admin uid=%s ended impersonation of uid=%s", admin_uid, target)
    return target


def get_impersonated_uid(admin_uid: int) -> Optional[int]:
    """Return the uid the admin is currently viewing as, or None."""
    return _impersonation.get(admin_uid)


def is_impersonating(admin_uid: int) -> bool:
    return admin_uid in _impersonation


# ── Impersonation banner ─────────────────────────────────────
def _imp_banner(target_uid: int, target_name: str) -> str:
    return (
        f"\n\n━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👁 *[ADMIN VIEW]* Viewing as `{target_uid}` ({target_name})\n"
        f"Type /exituser to return to Admin Panel."
    )


async def _send_imp_status(chat, target_uid: int) -> None:
    """Send the impersonation status bar as a pinned-style notice."""
    doc = col_users.find_one({"uid": target_uid}, {"name": 1, "username": 1}) or {}
    name  = doc.get("name", "?")
    uname = f"@{doc['username']}" if doc.get("username") else "—"
    await chat.send_message(
        f"👁 *Admin Impersonation Active*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 Target UID  : `{target_uid}`\n"
        f"👤 Name        : {name}\n"
        f"🔗 Username    : {uname}\n\n"
        f"You are now interacting with the bot *as this user*.\n"
        f"All actions (add, delete, OTP, settings) operate on their vault.\n\n"
        f"⚠️ _Every action is logged under `admin_imp_*` in the audit trail._\n"
        f"Type /exituser or press *🚪 Exit User View* to return to your admin panel.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_imp_active(),
    )


# ── Impersonation-mode keyboards ────────────────────────────
def rkb_imp_active() -> ReplyKeyboardMarkup:
    """Full user keyboard with an Exit button prepended."""
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("🚪 Exit User View")],
            [KeyboardButton("➕ Add Account"),   KeyboardButton("🔑 Get OTP")],
            [KeyboardButton("📋 My Accounts"),   KeyboardButton("🔍 Search")],
            [KeyboardButton("🔒 Lock Vault"),    KeyboardButton("⚙️ Settings")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


# ── Start impersonation ──────────────────────────────────────
async def _admin_enter_user(update_or_chat, ctx, admin_uid: int,
                             target_uid: int) -> None:
    """Put admin into impersonation mode for target_uid."""
    doc = col_users.find_one({"uid": target_uid}) or {}
    if not doc:
        chat = getattr(update_or_chat, "effective_chat", update_or_chat)
        await chat.send_message(
            f"❌ User `{target_uid}` not found in database.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return

    impersonate_start(admin_uid, target_uid)
    # Give admin an open session as the target user
    session_touch(target_uid)

    chat = getattr(update_or_chat, "effective_chat", update_or_chat)
    await _send_imp_status(chat, target_uid)

    # Show the target user's home screen
    name = doc.get("name", "User")
    count = col_accounts.count_documents({"uid": target_uid})
    pin_set = bool(db_get_pin(target_uid))
    paranoid = db_get_setting(target_uid, "paranoid", False)
    await chat.send_message(
        f"🏠 *Vault Home — {name}*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔐 {count} account{'s' if count != 1 else ''}\n"
        f"{'🔑' if pin_set else '🔓'} Passcode: {'Set' if pin_set else 'Not set'}\n"
        f"{'🔕 Paranoid mode ON' if paranoid else ''}"
        + _imp_banner(target_uid, name),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_imp_active(),
    )


# ── Exit impersonation ───────────────────────────────────────
async def _admin_exit_user(chat, ctx, admin_uid: int) -> None:
    """End impersonation and return admin to their panel."""
    target = impersonate_end(admin_uid)
    ctx.user_data.clear()
    ctx.user_data["admin_mode"] = True
    stats = db_global_stats()
    msg = (
        f"🚪 *Exited user view.*"
        + (f"\n_Was viewing `{target}`._" if target else "")
        + f"\n\n🛡 *Admin Panel*\n"
        f"👥 `{stats['total_users']}` users · "
        f"🔐 `{stats['total_accounts']}` accounts · "
        f"🔔 `{stats['pending_resets']}` pending resets"
    )
    await chat.send_message(msg, parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin())


# ── /exituser command ────────────────────────────────────────
async def cmd_exituser(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id
    if uid != ADMIN_ID:
        await update.message.reply_text("⛔ Admin only.")
        return
    if not is_impersonating(uid):
        await update.message.reply_text(
            "ℹ️ You are not in user-view mode.",
            reply_markup=rkb_admin(),
        )
        return
    await _admin_exit_user(update.effective_chat, ctx, uid)


# ── Impersonation-aware uid resolver ────────────────────────
def _effective_uid(real_uid: int) -> int:
    """
    If admin is impersonating someone, return the target uid.
    All DB operations should use this uid so they affect the target's vault.
    """
    if real_uid == ADMIN_ID:
        return _impersonation.get(real_uid, real_uid)
    return real_uid


# ── Impersonation interceptor for on_message ─────────────────
async def _handle_impersonation_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                         real_uid: int, text: str, state: str) -> bool:
    """
    Called at the very top of on_message when admin is impersonating.
    Returns True if the message was fully handled.
    Swaps uid → target and lets the normal flow run with the swapped uid.
    """
    if real_uid != ADMIN_ID or not is_impersonating(real_uid):
        return False

    target_uid = _impersonation[real_uid]

    # ── Exit button / command ────────────────────────────────
    if text in ("🚪 Exit User View", "/exituser"):
        await _admin_exit_user(update.effective_chat, ctx, real_uid)
        return True

    # ── Log every action under audit ────────────────────────
    audit(real_uid, "admin_imp_action", f"uid={target_uid} text={text[:48]}")

    # Patch ctx.user_data to be the TARGET user's data, stored under a
    # namespaced key in the admin's own user_data dict so it persists
    # across the session without leaking into other contexts.
    _ensure_imp_user_data(ctx, target_uid)

    # ── Inject the virtual session for the target user ───────
    # Keep target's session alive while admin is viewing it
    session_touch(target_uid)

    # ── Re-run the regular on_message logic with swapped uid ─
    # We do this by temporarily patching the update's effective_user.id.
    # Since Update is immutable, we use a wrapper approach instead:
    # call each relevant handler function directly with target_uid.
    # FIX BUG 13: wrap in try/finally so _save_imp_user_data always runs even
    # if _dispatch_as_user raises an exception mid-flight. Without this, any
    # unhandled error inside the dispatch would silently drop the target user's
    # ctx state, causing the next impersonation action to start from a blank slate.
    try:
        await _dispatch_as_user(update, ctx, target_uid, text, state)
    finally:
        _save_imp_user_data(ctx, target_uid)
    return True


# ── Impersonation interceptor for on_button ──────────────────
async def _handle_impersonation_callback(q, ctx, real_uid: int, data: str) -> bool:
    """
    Called at the very top of on_button when admin is impersonating.
    Returns True if callback was forwarded to user logic.
    """
    if real_uid != ADMIN_ID or not is_impersonating(real_uid):
        return False

    target_uid = _impersonation[real_uid]

    # Log
    audit(real_uid, "admin_imp_callback", f"uid={target_uid} data={data[:48]}")

    # Keep target session alive
    session_touch(target_uid)

    # Patch user_data namespace
    _ensure_imp_user_data(ctx, target_uid)

    # Let the normal callback router run — but uid will be resolved via
    # _effective_uid() inside on_button after we return False here.
    # Instead we need the normal flow to use target_uid, so we patch state.
    return False   # signal: continue into main callback router with effective uid swapped


# ── user_data namespace for impersonation ─────────────────────
_imp_user_data: dict[int, dict] = {}   # target_uid → their ctx-like user_data


def _ensure_imp_user_data(ctx, target_uid: int) -> None:
    """
    Swap ctx.user_data to a per-target namespace so the admin's own
    state isn't polluted by the target user's flow state.
    The impersonated user's state is stored in _imp_user_data[target_uid].
    """
    if target_uid not in _imp_user_data:
        _imp_user_data[target_uid] = {}
    # Temporarily replace the contents of ctx.user_data with the target's data.
    # We can't replace the dict object itself (PTB holds a reference), so we
    # mirror the contents in and out.
    ctx.user_data.clear()
    ctx.user_data.update(_imp_user_data[target_uid])


def _save_imp_user_data(ctx, target_uid: int) -> None:
    """Flush ctx.user_data back to the target's namespace after a dispatch."""
    _imp_user_data[target_uid] = dict(ctx.user_data)


# ── Central dispatch-as-user ─────────────────────────────────
async def _dispatch_as_user(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                              target_uid: int, text: str, state: str) -> None:
    """
    Re-run the standard on_message handler logic using target_uid as
    the effective uid. This gives the admin full access to the target
    user's vault: view accounts, get OTPs, manage settings, etc.
    """
    # ── PIN-related states in impersonation: skip for admin ──
    # Admin does not need to enter the target's PIN — we grant access directly.

    # ── CANCEL ──────────────────────────────────────────────
    if text == "❌ Cancel":
        _imp_user_data[target_uid] = {}
        ctx.user_data.clear()
        target_doc = col_users.find_one({"uid": target_uid}) or {}
        await update.effective_chat.send_message(
            home_text(target_uid, target_doc.get("name", "User"))
            + _imp_banner(target_uid, target_doc.get("name", "User")),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_imp_active(),
        )
        return

    # ── BACK ─────────────────────────────────────────────────
    if text == "🔙 Back":
        back_dest = ctx.user_data.get("back", "home")
        _imp_user_data[target_uid] = {}
        ctx.user_data.clear()
        target_doc = col_users.find_one({"uid": target_uid}) or {}
        tname = target_doc.get("name", "User")
        if back_dest == "settings":
            pin_set  = bool(db_get_pin(target_uid))
            paranoid = db_get_setting(target_uid, "paranoid", False)
            await update.effective_chat.send_message(
                f"⚙️ *Settings — {tname}*\n\n"
                f"🔑 Passcode: {'✅ Set' if pin_set else '❌ Not set'}\n"
                f"🔕 Paranoid: {'✅ ON' if paranoid else '❌ OFF'}"
                + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_settings(),
            )
        else:
            await update.effective_chat.send_message(
                home_text(target_uid, tname)
                + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_imp_active(),
            )
        return

    # ── Unlock Vault (admin bypasses PIN) ────────────────────
    if text == "🔓 Unlock Vault":
        session_touch(target_uid)
        target_doc = col_users.find_one({"uid": target_uid}) or {}
        await update.effective_chat.send_message(
            "✅ *Vault unlocked (admin access — PIN bypassed)*\n\n"
            + home_text(target_uid, target_doc.get("name", "User"))
            + _imp_banner(target_uid, target_doc.get("name", "User")),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_imp_active(),
        )
        _save_imp_user_data(ctx, target_uid)
        return

    # ── Wait-states ──────────────────────────────────────────
    if state == "WAIT_RESTORE":
        await _do_restore(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_SVC_NAME":
        await _do_save_svc_name(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_RENAME_ADD":
        await _do_rename_add(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_RENAME":
        await _do_rename(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_SEARCH":
        await _do_search(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_URI":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_add_uri(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_KEY":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_add_key(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_KEY_DIGITS":
        await _do_key_digits(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_KEY_PERIOD":
        await _do_key_period(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return

    # ── Admin sets a new passcode ON BEHALF of user ──────────
    if state == "WAIT_SET_PIN":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_set_pin(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return
    if state == "WAIT_CONFIRM_PIN":
        try: await update.message.delete()
        except TelegramError: pass
        await _do_confirm_pin(update, ctx, target_uid, text)
        _save_imp_user_data(ctx, target_uid); return

    # ── Main menu buttons ────────────────────────────────────
    target_doc = col_users.find_one({"uid": target_uid}) or {}
    tname = target_doc.get("name", "User")

    if text == "➕ Add Account":
        ctx.user_data.clear()
        ctx.user_data["back"] = "home"
        _cancel_refresh(target_uid)
        await update.effective_chat.send_message(
            "➕ *Add New Account*\n\nChoose how to add:"
            + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )

    elif text == "📷 Scan QR Code":
        ctx.user_data["state"] = "WAIT_QR"
        ctx.user_data["back"]  = "add"
        await update.effective_chat.send_message(
            "📷 Send the QR code image." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔗 Paste URI":
        ctx.user_data["state"] = "WAIT_URI"
        ctx.user_data["back"]  = "add"
        await update.effective_chat.send_message(
            "🔗 Send your `otpauth://` URI." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔐 Enter Secret Key":
        ctx.user_data["state"] = "WAIT_KEY"
        ctx.user_data["back"]  = "add"
        await update.effective_chat.send_message(
            "🔐 Send the base32 secret key." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_add(),
        )

    elif text == "🔑 Get OTP":
        docs = db_list(target_uid)
        if not docs:
            await update.effective_chat.send_message(
                "📭 No accounts in this vault." + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_imp_active(),
            )
        else:
            _cancel_refresh(target_uid)
            docs_sorted = sorted(docs, key=lambda x: (not x.get("starred", False), x["svc"].lower()))
            paranoid = db_get_setting(target_uid, "paranoid", False)
            await update.effective_chat.send_message(
                f"🔑 *{tname}'s OTP Codes* — {len(docs_sorted)} account{'s' if len(docs_sorted)!=1 else ''}"
                + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_imp_active(),
            )
            for doc in docs_sorted:
                svc = doc["svc"]
                full_doc = db_get(target_uid, svc)
                if not full_doc: continue
                try:
                    secret = aes_decrypt(full_doc["enc"])
                except Exception:
                    await update.effective_chat.send_message(f"🔐 *{svc}* — decryption failed.")
                    continue
                otp_type = full_doc.get("type", "totp")
                counter  = full_doc.get("counter", 0)
                if otp_type == "hotp":
                    counter = db_hotp_increment(target_uid, svc)
                otp_msg = await update.effective_chat.send_message(
                    otp_text(svc, full_doc.get("issuer", svc), secret,
                             full_doc.get("digits", 6), full_doc.get("period", 30),
                             full_doc.get("algorithm", "SHA1"), otp_type, counter),
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=ikb_otp_view(svc),
                )
                if otp_type == "totp":
                    asyncio.create_task(
                        _otp_refresh_loop(
                            otp_msg.chat_id, otp_msg.message_id,
                            target_uid, svc, full_doc, secret, ctx.bot, paranoid,
                            no_inline=True,
                        )
                    )

    elif text == "📋 My Accounts":
        docs = db_list(target_uid)
        if not docs:
            await update.effective_chat.send_message(
                "📭 Vault is empty." + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_imp_active(),
            )
        else:
            ctx.user_data["back"] = "home"
            await update.effective_chat.send_message(
                f"📋 *{tname}'s Vault* — {len(docs)} account{'s' if len(docs)!=1 else ''}"
                + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_imp_active(),
            )
            await update.effective_chat.send_message(
                "👇 Choose an account:",
                reply_markup=ikb_accounts(docs, "DETAIL", uid=target_uid),
            )

    elif text == "🔍 Search":
        ctx.user_data["state"] = "WAIT_SEARCH"
        ctx.user_data["back"]  = "home"
        await update.effective_chat.send_message(
            "🔍 Type any part of the name or issuer." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🗑 Delete Account":
        docs = db_list(target_uid)
        if not docs:
            await update.effective_chat.send_message(
                "📭 Nothing to delete.", reply_markup=rkb_settings()
            )
        else:
            ctx.user_data["back"] = "settings"
            await update.effective_chat.send_message(
                "🗑 Choose an account to delete:" + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_back_settings(),
            )
            await update.effective_chat.send_message(
                "👇", reply_markup=ikb_accounts(docs, "DEL_ASK", uid=target_uid),
            )

    elif text == "✏️ Rename":
        docs = db_list(target_uid)
        if not docs:
            await update.effective_chat.send_message("📭 No accounts to rename.", reply_markup=rkb_settings())
        else:
            ctx.user_data["back"] = "settings"
            await update.effective_chat.send_message(
                "✏️ Choose an account to rename:" + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_back_settings(),
            )
            await update.effective_chat.send_message(
                "👇", reply_markup=ikb_accounts(docs, "RENAME_CB", uid=target_uid),
            )

    elif text == "💾 Backup":
        await _do_backup(update, target_uid)

    elif text == "📥 Restore":
        ctx.user_data["state"] = "WAIT_RESTORE"
        ctx.user_data["back"]  = "settings"
        await update.effective_chat.send_message(
            "📥 Paste the encrypted backup string." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_cancel_settings(),
        )

    elif text == "🔒 Lock Vault":
        _cancel_refresh(target_uid)
        session_kill(target_uid)
        await update.effective_chat.send_message(
            f"🔒 *{tname}'s vault locked.*" + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_imp_active(),
        )

    elif text == "⚙️ Settings":
        ctx.user_data.clear()
        ctx.user_data["back"] = "home"
        pin_set  = bool(db_get_pin(target_uid))
        paranoid = db_get_setting(target_uid, "paranoid", False)
        await update.effective_chat.send_message(
            f"⚙️ *Settings — {tname}*\n\n"
            f"🔑 Passcode: {'✅ Set' if pin_set else '❌ Not set'}\n"
            f"🔕 Paranoid: {'✅ ON' if paranoid else '❌ OFF'}"
            + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )

    elif text == "🔑 Set Passcode":
        ctx.user_data["state"] = "WAIT_SET_PIN"
        ctx.user_data["back"]  = "settings"
        await update.effective_chat.send_message(
            "🔑 Send a 4–8 digit PIN for this user.\n_Message deleted immediately._"
            + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel_settings(),
        )

    elif text == "🔓 Remove Passcode":
        if not db_get_pin(target_uid):
            await update.effective_chat.send_message("ℹ️ No passcode set.", reply_markup=rkb_settings())
        else:
            db_set_pin(target_uid, None)
            audit(target_uid, "admin_imp_pin_removed", str(ADMIN_ID))
            await update.effective_chat.send_message(
                f"✅ *Passcode removed for {tname}.*" + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_settings(),
            )

    elif text == "🔕 Paranoid Mode":
        current = db_get_setting(target_uid, "paranoid", False)
        db_set_setting(target_uid, "paranoid", not current)
        state_str = "ON ✅" if not current else "OFF ❌"
        await update.effective_chat.send_message(
            f"🔕 *Paranoid mode {state_str} for {tname}*" + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_settings(),
        )

    elif text == "📊 My Stats":
        ctx.user_data["back"] = "settings"
        await _do_stats_for(update, target_uid, tname)

    elif text == "🕐 Session Info":
        ctx.user_data["back"] = "settings"
        session_doc = col_sessions.find_one({"uid": target_uid})
        if session_doc:
            last    = session_doc.get("last")
            if last and last.tzinfo is None:
                last = last.replace(tzinfo=timezone.utc)
            elapsed   = int((datetime.now(timezone.utc) - last).total_seconds()) if last else SESSION_TTL
            remaining = max(0, SESSION_TTL - elapsed)
            mins, secs = divmod(remaining, 60)
            await update.effective_chat.send_message(
                f"🕐 *Session — {tname}*\n"
                f"⏳ Remaining: *{mins}m {secs}s*"
                + _imp_banner(target_uid, tname),
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_back_settings(),
            )
        else:
            await update.effective_chat.send_message(
                f"ℹ️ No active session for {tname}." + _imp_banner(target_uid, tname),
                reply_markup=rkb_back_settings(),
            )

    elif text == "❓ Help":
        ctx.user_data["back"] = "settings"
        await update.effective_chat.send_message(
            "ℹ️ Help is shown normally for this user." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_back_settings(),
        )

    else:
        await update.effective_chat.send_message(
            "ℹ️ Use the keyboard to navigate." + _imp_banner(target_uid, tname),
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_imp_active(),
        )

    _save_imp_user_data(ctx, target_uid)


async def _do_stats_for(update: Update, target_uid: int, tname: str) -> None:
    """Stats display for impersonation mode — reuses _do_stats logic with target uid."""
    pipeline = [
        {"$match": {"uid": target_uid}},
        {"$group": {
            "_id":    None,
            "total":  {"$sum": 1},
            "oldest": {"$min": "$created"},
            "newest": {"$max": "$created"},
        }},
    ]
    agg = list(col_accounts.aggregate(pipeline))
    total = oldest = newest = None
    if agg:
        total  = agg[0]["total"]
        oldest = agg[0]["oldest"].strftime("%Y-%m-%d") if agg[0]["oldest"] else "—"
        newest = agg[0]["newest"].strftime("%Y-%m-%d") if agg[0]["newest"] else "—"
    else:
        total = 0
    pin_set  = bool(db_get_pin(target_uid))
    paranoid = db_get_setting(target_uid, "paranoid", False)
    starred  = col_accounts.count_documents({"uid": target_uid, "starred": True})
    await update.effective_chat.send_message(
        f"📊 *Stats — {tname}*\n━━━━━━━━━━━━━━━━\n"
        f"🔐 Accounts   : `{total}`\n"
        f"⭐ Starred    : `{starred}`\n"
        f"🗓 Oldest     : `{oldest or '—'}`\n"
        f"🆕 Newest     : `{newest or '—'}`\n"
        f"🔑 Passcode   : {'✅ Set' if pin_set else '❌ Not set'}\n"
        f"🔕 Paranoid   : {'✅ ON' if paranoid else '❌ OFF'}"
        + _imp_banner(target_uid, tname),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_back_settings(),
    )


# ── Wire impersonation into on_button's uid resolution ───────
# on_button already calls _effective_uid() via the session_touch line;
# we need to ensure all DB calls inside on_button use the right uid.
# We do this by patching the uid variable at the start of on_button
# when admin is impersonating.  The patch is added in on_button below.

# ─────────────────────────────────────────────────────────────
# 25.  ADVANCED ADMIN PANEL FEATURES
# ─────────────────────────────────────────────────────────────

# ── Runtime config store (in-memory, persisted to MongoDB) ───
_runtime_config_col = _db["runtime_config"]

def rc_get(key: str, default=None):
    """Get a runtime config value from MongoDB."""
    doc = _runtime_config_col.find_one({"key": key})
    return doc["value"] if doc else default

def rc_set(key: str, value) -> None:
    """Set a runtime config value in MongoDB."""
    _runtime_config_col.update_one(
        {"key": key}, {"$set": {"key": key, "value": value, "updated": datetime.now(timezone.utc)}},
        upsert=True,
    )

def rc_delete(key: str) -> None:
    _runtime_config_col.delete_one({"key": key})


# ── Maintenance mode ─────────────────────────────────────────
def is_maintenance_mode() -> bool:
    return bool(rc_get("maintenance_mode", False))

def set_maintenance_mode(on: bool) -> None:
    rc_set("maintenance_mode", on)
    audit(ADMIN_ID, "admin_maintenance_mode", "on" if on else "off")
    log.info("Maintenance mode: %s", "ON" if on else "OFF")


# ── Registration lock ────────────────────────────────────────
def is_registration_locked() -> bool:
    return bool(rc_get("registration_locked", False))

def set_registration_lock(locked: bool) -> None:
    rc_set("registration_locked", locked)
    audit(ADMIN_ID, "admin_registration_lock", "locked" if locked else "unlocked")


# ── Account cap per user ─────────────────────────────────────
def get_account_cap() -> int:
    return int(rc_get("account_cap", 0))  # 0 = no limit

def set_account_cap(cap: int) -> None:
    rc_set("account_cap", cap)
    audit(ADMIN_ID, "admin_account_cap", str(cap))


# ── Scheduled broadcast ──────────────────────────────────────
_scheduled_broadcasts: dict[str, asyncio.Task] = {}

def db_save_scheduled_broadcast(broadcast_id: str, message: str, run_at: datetime) -> None:
    _db["scheduled_broadcasts"].update_one(
        {"broadcast_id": broadcast_id},
        {"$set": {
            "broadcast_id": broadcast_id,
            "message": message,
            "run_at": run_at,
            "status": "pending",
            "created": datetime.now(timezone.utc),
        }},
        upsert=True,
    )

def db_get_scheduled_broadcasts() -> list:
    return list(_db["scheduled_broadcasts"].find(
        {"status": "pending"},
        {"_id": 0}
    ).sort("run_at", 1))

def db_cancel_scheduled_broadcast(broadcast_id: str) -> None:
    _db["scheduled_broadcasts"].update_one(
        {"broadcast_id": broadcast_id},
        {"$set": {"status": "cancelled"}},
    )


def db_complete_scheduled_broadcast(broadcast_id: str) -> None:
    # FIX BUG 4: separate "sent" status so completed broadcasts are distinguishable
    # from admin-cancelled ones in the DB and audit log.
    _db["scheduled_broadcasts"].update_one(
        {"broadcast_id": broadcast_id},
        {"$set": {"status": "sent", "completed": datetime.now(timezone.utc)}},
    )


async def _run_scheduled_broadcast(broadcast_id: str, message: str, delay: float) -> None:
    """Sleep then send a broadcast."""
    await asyncio.sleep(delay)
    db_complete_scheduled_broadcast(broadcast_id)  # FIX BUG 4: was db_cancel_scheduled_broadcast — now sets status="sent"
    users = list(col_users.find({}, {"uid": 1}))
    sent = failed = blocked = 0
    for u in users:
        try:
            await _bot_ref.send_message(
                u["uid"],
                f"📢 *Scheduled Announcement*\n\n{message}",
                parse_mode=ParseMode.MARKDOWN,
            )
            sent += 1
        except TelegramError as e:
            err = str(e).lower()
            if any(x in err for x in ("blocked", "deactivated", "not found", "forbidden")):
                blocked += 1
            else:
                failed += 1
        await asyncio.sleep(0.05)
    audit(ADMIN_ID, "admin_scheduled_broadcast_done", f"id={broadcast_id} sent={sent}")
    try:
        await _bot_ref.send_message(
            ADMIN_ID,
            f"📢 *Scheduled broadcast done*\n• Sent: `{sent}`\n• Blocked: `{blocked}`\n• Errors: `{failed}`",
            parse_mode=ParseMode.MARKDOWN,
        )
    except TelegramError:
        pass


# ── Admin notes on users ─────────────────────────────────────
def db_set_admin_note(target_uid: int, note: str) -> None:
    col_users.update_one(
        {"uid": target_uid},
        {"$set": {"admin_note": note, "admin_note_at": datetime.now(timezone.utc)}},
    )

def db_get_admin_note(target_uid: int) -> Optional[str]:
    doc = col_users.find_one({"uid": target_uid}, {"admin_note": 1})
    return (doc or {}).get("admin_note")


# ── User activity heatmap data ───────────────────────────────
def db_activity_heatmap(days: int = 30) -> list:
    """Returns per-day action counts for the last N days."""
    since = datetime.now(timezone.utc) - timedelta(days=days)
    pipe = [
        {"$match": {"ts": {"$gte": since}}},
        {"$group": {
            "_id": {"$dateToString": {"format": "%Y-%m-%d", "date": "$ts"}},
            "count": {"$sum": 1},
        }},
        {"$sort": {"_id": 1}},
    ]
    return list(col_audit.aggregate(pipe))


# ── Growth metrics ───────────────────────────────────────────
def db_growth_metrics() -> dict:
    """Returns new users per day for the last 14 days."""
    since = datetime.now(timezone.utc) - timedelta(days=14)
    pipe = [
        {"$match": {"joined": {"$gte": since}}},
        {"$group": {
            "_id": {"$dateToString": {"format": "%Y-%m-%d", "date": "$joined"}},
            "count": {"$sum": 1},
        }},
        {"$sort": {"_id": 1}},
    ]
    return {r["_id"]: r["count"] for r in col_users.aggregate(pipe)}


# ── Admin notes keyboard ─────────────────────────────────────
def ikb_admin_user_actions_v2(target_uid: int, banned: bool) -> InlineKeyboardMarkup:
    """Extended user action keyboard with note + whitelist buttons."""
    ban_label = "✅ Unban" if banned else "🚫 Ban"
    ban_cb    = f"ADMIN_UNBAN:{target_uid}" if banned else f"ADMIN_BAN:{target_uid}"
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(ban_label,             callback_data=ban_cb),
            InlineKeyboardButton("🗑 Delete All Data",   callback_data=f"ADMIN_DEL_USER:{target_uid}"),
        ],
        [
            InlineKeyboardButton("🔒 Force Lock",       callback_data=f"ADMIN_LOCK:{target_uid}"),
            InlineKeyboardButton("💬 Send Message",      callback_data=f"ADMIN_MSG:{target_uid}"),
        ],
        [
            InlineKeyboardButton("📋 Audit Trail",      callback_data=f"ADMIN_AUDIT:{target_uid}"),
            InlineKeyboardButton("📊 User Stats",        callback_data=f"ADMIN_USTATS:{target_uid}"),
        ],
        [
            InlineKeyboardButton("👤 Login as User",    callback_data=f"ADMIN_IMPERSONATE:{target_uid}"),
            InlineKeyboardButton("📝 Add Note",          callback_data=f"ADMIN_NOTE:{target_uid}"),
        ],
        [
            InlineKeyboardButton("🔓 Force Unlock",     callback_data=f"ADMIN_FORCEUNLOCK:{target_uid}"),
            InlineKeyboardButton("📤 Export User Data",  callback_data=f"ADMIN_EXPORTUSER:{target_uid}"),
        ],
    ])


# Replace the original so all existing callers get the extended buttons
ikb_admin_user_actions = ikb_admin_user_actions_v2


# ── Advanced admin keyboards ─────────────────────────────────
def rkb_admin_v2() -> ReplyKeyboardMarkup:
    """Extended admin panel keyboard with all advanced features."""
    return ReplyKeyboardMarkup(
        [
            [KeyboardButton("👥 Users"),            KeyboardButton("📊 Global Stats")],
            [KeyboardButton("📋 Audit Log"),         KeyboardButton("🔔 Pending Resets")],
            [KeyboardButton("📢 Broadcast"),          KeyboardButton("🗓 Schedule Broadcast")],
            [KeyboardButton("🔍 User Lookup"),        KeyboardButton("🔎 Search Accounts")],
            [KeyboardButton("🚫 Ban User"),           KeyboardButton("✅ Unban User")],
            [KeyboardButton("🗑 Delete User"),        KeyboardButton("💬 Message User")],
            [KeyboardButton("🔒 Force Lock User"),    KeyboardButton("📤 Export All Logs")],
            [KeyboardButton("👤 Login as User"),      KeyboardButton("⚙️ Bot Config")],
            [KeyboardButton("🛡 Security Center"),    KeyboardButton("📈 Growth Stats")],
            [KeyboardButton("🔧 Runtime Settings"),   KeyboardButton("📊 Activity Heatmap")],
            [KeyboardButton("📋 Scheduled Broadcasts"),KeyboardButton("🔄 Bot Health")],
            [KeyboardButton("🏠 Home")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


# ── Advanced admin: security center ─────────────────────────
@admin_only
async def _admin_security_center(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Show security overview: suspicious activity, multiple fails, etc."""
    now = datetime.now(timezone.utc)
    since_1h = now - timedelta(hours=1)
    since_24h = now - timedelta(hours=24)

    # Failed PIN attempts in last 24h
    pin_fails_pipe = [
        {"$match": {"action": "pin_fail", "ts": {"$gte": since_24h}}},
        {"$group": {"_id": "$uid", "count": {"$sum": 1}}},
        {"$match": {"count": {"$gte": 3}}},
        {"$sort": {"count": -1}},
        {"$limit": 10},
    ]
    pin_fail_users = list(col_audit.aggregate(pin_fails_pipe))

    # Rapid OTP generation (possible abuse)
    otp_pipe = [
        {"$match": {"action": {"$in": ["otp_get", "otp_copy"]}, "ts": {"$gte": since_1h}}},
        {"$group": {"_id": "$uid", "count": {"$sum": 1}}},
        {"$match": {"count": {"$gte": 20}}},
        {"$sort": {"count": -1}},
        {"$limit": 5},
    ]
    otp_abuse = list(col_audit.aggregate(otp_pipe))

    # Export events in last 24h
    export_count = col_audit.count_documents({"action": "export", "ts": {"$gte": since_24h}})

    # New accounts with no activity (potential bots)
    phantom_count = col_users.count_documents({
        "joined": {"$gte": now - timedelta(days=7)},
        "last_seen": {"$exists": False},
    })

    lines = []
    if pin_fail_users:
        lines.append("*🔑 High PIN Fail Rate (24h):*")
        for r in pin_fail_users:
            doc = col_users.find_one({"uid": r["_id"]}, {"name": 1}) or {}
            lines.append(f"  `{r['_id']}` {doc.get('name','?')[:12]} — {r['count']} fails")
    if otp_abuse:
        lines.append("\n*⚡ Rapid OTP Generation (1h):*")
        for r in otp_abuse:
            doc = col_users.find_one({"uid": r["_id"]}, {"name": 1}) or {}
            lines.append(f"  `{r['_id']}` {doc.get('name','?')[:12]} — {r['count']} OTPs")

    summary = (
        f"🛡 *Security Center*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔑 Users with 3+ PIN fails (24h) : `{len(pin_fail_users)}`\n"
        f"⚡ OTP abuse suspects (1h)       : `{len(otp_abuse)}`\n"
        f"📤 Export events (24h)           : `{export_count}`\n"
        f"👻 Phantom accounts (7d)         : `{phantom_count}`\n"
    )
    if lines:
        summary += "\n" + "\n".join(lines)
    else:
        summary += "\n✅ _No anomalies detected._"

    await update.effective_chat.send_message(
        summary, parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
    )


# ── Advanced admin: growth stats ─────────────────────────────
@admin_only
async def _admin_growth_stats(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Show user growth over time."""
    growth = db_growth_metrics()
    now    = datetime.now(timezone.utc)

    # Retention: users active in last 7d vs total
    active_7d  = col_sessions.count_documents({
        "last": {"$gte": now - timedelta(days=7)},
    })
    total      = col_users.count_documents({})
    retention  = f"{100 * active_7d // total}%" if total else "N/A"

    # Accounts per user distribution
    pipe = [
        {"$group": {"_id": "$uid", "count": {"$sum": 1}}},
        {"$group": {"_id": None, "avg": {"$avg": "$count"}, "max": {"$max": "$count"}}},
    ]
    agg  = list(col_accounts.aggregate(pipe))
    avg_accts = round(agg[0]["avg"], 1) if agg else 0
    max_accts = agg[0]["max"]           if agg else 0

    if growth:
        bar_lines = []
        max_count = max(growth.values()) or 1
        for date, count in list(growth.items())[-14:]:
            bar_len = int(12 * count / max_count)
            bar     = "█" * bar_len + "░" * (12 - bar_len)
            bar_lines.append(f"`{date[5:]}` {bar} `{count}`")
        chart = "\n".join(bar_lines)
    else:
        chart = "_No data_"

    await update.effective_chat.send_message(
        f"📈 *Growth Stats (14d)*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Total users          : `{total}`\n"
        f"🔄 Active last 7d       : `{active_7d}` ({retention} retention)\n"
        f"🔐 Avg accounts/user    : `{avg_accts}`\n"
        f"🏆 Max accounts (1 user): `{max_accts}`\n\n"
        f"*New users per day:*\n{chart}",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Advanced admin: activity heatmap ─────────────────────────
@admin_only
async def _admin_activity_heatmap(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Show audit event activity per day for last 30 days as ASCII chart."""
    rows = db_activity_heatmap(30)
    if not rows:
        await update.effective_chat.send_message(
            "📊 No activity data.", reply_markup=rkb_admin_back()
        )
        return
    max_count = max(r["count"] for r in rows) or 1
    lines     = []
    for r in rows:
        bar_len = int(15 * r["count"] / max_count)
        bar     = "█" * bar_len + "░" * (15 - bar_len)
        lines.append(f"`{r['_id'][5:]}` {bar} `{r['count']}`")
    await update.effective_chat.send_message(
        f"📊 *Activity Heatmap (30d)*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n" + "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Advanced admin: runtime settings ─────────────────────────
@admin_only
async def _admin_runtime_settings(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Show toggleable runtime settings panel."""
    maint = is_maintenance_mode()
    reg_locked = is_registration_locked()
    cap = get_account_cap()
    await update.effective_chat.send_message(
        f"🔧 *Runtime Settings*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🚧 Maintenance mode   : {'🟢 ON' if maint else '⚫ OFF'}\n"
        f"🔒 Registration lock  : {'🟢 LOCKED' if reg_locked else '⚫ OPEN'}\n"
        f"📦 Account cap/user   : `{'No limit' if not cap else cap}`\n\n"
        f"_Use the buttons below to toggle settings._",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb_runtime_settings(maint, reg_locked, cap),
    )


def ikb_runtime_settings(maint: bool, reg_locked: bool, cap: int) -> InlineKeyboardMarkup:
    maint_label = "🔴 Disable Maintenance" if maint else "🟢 Enable Maintenance"
    reg_label   = "🔓 Unlock Registration" if reg_locked else "🔒 Lock Registration"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(maint_label,        callback_data="ADMIN_RT_MAINT_TOGGLE")],
        [InlineKeyboardButton(reg_label,          callback_data="ADMIN_RT_REG_TOGGLE")],
        [InlineKeyboardButton("📦 Set Account Cap", callback_data="ADMIN_RT_CAP_SET")],
        [InlineKeyboardButton("❌ Close",           callback_data="ADMIN_CANCEL")],
    ])


# ── Advanced admin: bot health ────────────────────────────────
@admin_only
async def _admin_bot_health(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Show bot runtime health: uptime, DB stats, memory."""
    import sys
    try:
        import psutil
        proc   = psutil.Process()
        mem_mb = proc.memory_info().rss / 1024 / 1024
        cpu    = proc.cpu_percent(interval=0.2)
        mem_str = f"`{mem_mb:.1f} MB`"
        cpu_str = f"`{cpu:.1f}%`"
    except ImportError:
        mem_str = "_psutil not installed_"
        cpu_str = "_psutil not installed_"

    # DB collection sizes
    def col_info(col_name):
        try:
            stats = _db.command("collstats", col_name)
            count = stats.get("count", 0)
            size  = stats.get("storageSize", 0) // 1024
            return f"`{count}` docs / `{size}` KB"
        except Exception:
            return "_unavailable_"

    now    = datetime.now(timezone.utc)
    maint  = is_maintenance_mode()
    reg_ok = not is_registration_locked()

    py_ver = f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}"

    st = db_mongo_storage_info()
    if st["ok"]:
        bar_line      = f"\n`{st['bar']}` {st['pct_used']}" if st.get("bar") else ""
        storage_block = (
            f"\n\n🗄 *MongoDB Storage*\n"
            f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
            f"📦 Data          : `{st['data']}`\n"
            f"💽 Allocated     : `{st['storage']}`\n"
            f"🔑 Indexes       : `{st['indexes']}`\n"
            f"🆓 Free space    : `{st['free']}`{bar_line}\n"
            f"📄 Documents     : `{st['objects']:,}`"
        )
    else:
        storage_block = f"\n\n🗄 *MongoDB Storage*: _{st.get('error', 'unavailable')}_"

    await update.effective_chat.send_message(
        f"🔄 *Bot Health*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🐍 Python        : `{py_ver}`\n"
        f"💾 Memory        : {mem_str}\n"
        f"⚙️ CPU            : {cpu_str}\n"
        f"🛢 users         : {col_info('users')}\n"
        f"🛢 otp_accounts  : {col_info('otp_accounts')}\n"
        f"🛢 sessions      : {col_info('sessions')}\n"
        f"🛢 audit_log     : {col_info('audit_log')}\n"
        f"🚧 Maintenance   : {'🟢 ON' if maint else '⚫ OFF'}\n"
        f"🔒 Registration  : {'🔒 LOCKED' if not reg_ok else '🔓 OPEN'}\n"
        f"🕐 Server time   : `{now.strftime('%Y-%m-%d %H:%M UTC')}`\n"
        f"🔑 Admin sessions: `{len(_session_cache)}`\n"
        f"⏳ Auto-lock tasks: `{len(_auto_lock_tasks)}`"
        + storage_block,
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_back(),
    )


# ── Advanced admin: search accounts globally ─────────────────
@admin_only
async def _admin_search_accounts(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_ACCT_SEARCH"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🔎 *Global Account Search*\n\nSend a service name or keyword to search across ALL users' accounts.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


async def _admin_do_account_search(update: Update, ctx: ContextTypes.DEFAULT_TYPE, query: str) -> None:
    regex  = re.compile(re.escape(query), re.IGNORECASE)
    docs   = list(col_accounts.find(
        {"$or": [{"svc": regex}, {"issuer": regex}]},
        {"uid": 1, "svc": 1, "issuer": 1, "created": 1, "_id": 0},
    ).limit(20))
    if not docs:
        await update.effective_chat.send_message(
            f"🔎 No accounts found matching `{query}`.",
            parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
        )
        return
    lines = []
    for d in docs:
        user_doc = col_users.find_one({"uid": d["uid"]}, {"name": 1}) or {}
        lines.append(
            f"🔐 `{d['svc']}` · `{d.get('issuer','')[:12]}` — uid:`{d['uid']}` ({user_doc.get('name','?')[:10]})"
        )
    await update.effective_chat.send_message(
        f"🔎 *Search results for* `{query}` *(top {len(docs)})*\n"
        f"━━━━━━━━━━━━━━━━━━━━━━━━\n" + "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_admin_back(),
    )


# ── Advanced admin: schedule broadcast ──────────────────────
@admin_only
async def _admin_start_schedule_broadcast(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data["state"]      = "ADMIN_WAIT_SCHED_MSG"
    ctx.user_data["admin_mode"] = True
    await update.effective_chat.send_message(
        "🗓 *Schedule Broadcast*\n\n"
        "Step 1 of 2 — Send the message text to broadcast.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_cancel(),
    )


# ── Advanced admin: view scheduled broadcasts ────────────────
@admin_only
async def _admin_view_scheduled(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    rows = db_get_scheduled_broadcasts()
    if not rows:
        await update.effective_chat.send_message(
            "🗓 No scheduled broadcasts.",
            reply_markup=rkb_admin_back(),
        )
        return
    lines = []
    for r in rows:
        run_at = r["run_at"].strftime("%m-%d %H:%M UTC") if isinstance(r.get("run_at"), datetime) else "?"
        msg_preview = r.get("message", "")[:40] + ("…" if len(r.get("message","")) > 40 else "")
        lines.append(f"🗓 `{run_at}` — {msg_preview}\n  ID: `{r['broadcast_id'][:8]}`")
    ikb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"❌ Cancel {r['broadcast_id'][:8]}", callback_data=f"ADMIN_SCHED_CANCEL:{r['broadcast_id']}")]
        for r in rows[:5]
    ])
    await update.effective_chat.send_message(
        f"🗓 *Scheduled Broadcasts* ({len(rows)})\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n" + "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=ikb,
    )


# ── Advanced admin: export single user data ──────────────────
async def _admin_export_user_data(q, target_uid: int) -> None:
    """Export all data for a single user as a JSON file."""
    user_doc  = col_users.find_one({"uid": target_uid}, {"_id": 0, "pin_hash": 0, "security_answers_enc": 0}) or {}
    accts     = list(col_accounts.find({"uid": target_uid}, {"_id": 0, "enc": 0}))
    audit_log = list(col_audit.find({"uid": target_uid}, {"_id": 0}).sort("ts", -1).limit(200))

    # Serialize datetimes
    def _ser(obj):
        if isinstance(obj, datetime):
            return obj.isoformat()
        raise TypeError

    payload = {
        "user": user_doc,
        "accounts": [
            {k: (_ser(v) if isinstance(v, datetime) else v) for k, v in a.items()}
            for a in accts
        ],
        "audit_log": [
            {k: (_ser(v) if isinstance(v, datetime) else v) for k, v in r.items()}
            for r in audit_log
        ],
        "exported_at": datetime.now(timezone.utc).isoformat(),
    }
    bio  = io.BytesIO(json.dumps(payload, indent=2, default=str).encode())
    bio.name = f"nexauth_user_{target_uid}_{datetime.now(timezone.utc).strftime('%Y%m%d')}.json"
    try:
        await q.bot.send_document(
            chat_id=ADMIN_ID,
            document=bio,
            caption=f"📤 *User data export for* `{target_uid}`",
            parse_mode=ParseMode.MARKDOWN,
        )
        audit(ADMIN_ID, "admin_export_user", str(target_uid))
    except TelegramError as e:
        await q.message.reply_text(f"❌ Export failed: {e}")


# ── Advanced admin: force-unlock user ────────────────────────
async def _admin_force_unlock(q, target_uid: int) -> None:
    """Open a session for a user without a PIN check."""
    session_touch(target_uid)
    audit(target_uid, "admin_force_unlock", str(ADMIN_ID))
    await q.message.reply_text(
        f"🔓 *User `{target_uid}` session force-unlocked.*\nThey can now access their vault.",
        parse_mode=ParseMode.MARKDOWN,
    )
    try:
        await q.bot.send_message(
            chat_id=target_uid,
            text="🔓 *Your vault has been unlocked by the admin.*\nYou can now access your accounts.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
        )
    except TelegramError:
        pass


# ── Patch _handle_admin_message to include new features ──────
_orig_handle_admin_message = _handle_admin_message

async def _handle_admin_message_v2(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                                    uid: int, text: str, state: str) -> bool:
    """
    Extended admin message handler.
    Calls the original handler first, then handles new advanced features.
    """
    # Handle new admin panel navigation first (before original, to switch keyboard)
    if uid != ADMIN_ID:
        return False

    # Upgrade keyboard: switch to v2 admin keyboard when returning to panel
    if text == "🔙 Admin Panel":
        ctx.user_data.clear()
        ctx.user_data["admin_mode"] = True
        stats = db_global_stats()
        maint = "⚠️ MAINTENANCE ON" if is_maintenance_mode() else ""
        await update.effective_chat.send_message(
            "🛡 *Admin Panel v2*\n"
            f"👥 `{stats['total_users']}` users · 🔐 `{stats['total_accounts']}` accounts · "
            f"🔔 `{stats['pending_resets']}` pending resets"
            + (f"\n\n{maint}" if maint else ""),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_v2(),
        )
        return True

    # New advanced features
    if text == "🛡 Security Center":
        await _admin_security_center(update, ctx)
        return True
    if text == "📈 Growth Stats":
        await _admin_growth_stats(update, ctx)
        return True
    if text == "📊 Activity Heatmap":
        await _admin_activity_heatmap(update, ctx)
        return True
    if text == "🔧 Runtime Settings":
        await _admin_runtime_settings(update, ctx)
        return True
    if text == "🔄 Bot Health":
        await _admin_bot_health(update, ctx)
        return True
    if text == "🔎 Search Accounts":
        await _admin_search_accounts(update, ctx)
        return True
    if text == "🗓 Schedule Broadcast":
        await _admin_start_schedule_broadcast(update, ctx)
        return True
    if text == "📋 Scheduled Broadcasts":
        await _admin_view_scheduled(update, ctx)
        return True

    # New wait states
    if state == "ADMIN_WAIT_ACCT_SEARCH":
        ctx.user_data.pop("state", None)
        await _admin_do_account_search(update, ctx, text.strip())
        return True

    if state == "ADMIN_WAIT_SCHED_MSG":
        ctx.user_data["sched_msg"]  = text
        ctx.user_data["state"]      = "ADMIN_WAIT_SCHED_TIME"
        await update.effective_chat.send_message(
            "🗓 *Schedule Broadcast*\n\n"
            "Step 2 of 2 — In how many minutes should it be sent?\n"
            "_(Send a number, e.g. `60` for 1 hour from now)_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_cancel(),
        )
        return True

    if state == "ADMIN_WAIT_SCHED_TIME":
        ctx.user_data.pop("state", None)
        msg_text = ctx.user_data.pop("sched_msg", "")
        try:
            minutes = int(text.strip())
            if minutes < 1 or minutes > 10080:  # 1 min to 1 week
                raise ValueError
        except ValueError:
            await update.effective_chat.send_message(
                "❌ Invalid time. Send a number of minutes (1–10080).",
                reply_markup=rkb_admin_back(),
            )
            return True
        broadcast_id = base64.urlsafe_b64encode(os.urandom(6)).decode().rstrip("=")
        run_at       = datetime.now(timezone.utc) + timedelta(minutes=minutes)
        db_save_scheduled_broadcast(broadcast_id, msg_text, run_at)
        delay        = minutes * 60.0
        task         = asyncio.ensure_future(_run_scheduled_broadcast(broadcast_id, msg_text, delay))
        _scheduled_broadcasts[broadcast_id] = task
        audit(ADMIN_ID, "admin_schedule_broadcast", f"id={broadcast_id} delay={minutes}m")
        await update.effective_chat.send_message(
            f"✅ *Broadcast scheduled!*\n"
            f"🗓 Fires in `{minutes}` minute(s) at `{run_at.strftime('%H:%M UTC')}`\n"
            f"ID: `{broadcast_id[:8]}`",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return True

    if state == "ADMIN_WAIT_NOTE":
        ctx.user_data.pop("state", None)
        note_uid = ctx.user_data.pop("admin_note_uid", None)
        if note_uid:
            db_set_admin_note(note_uid, text.strip())
            audit(ADMIN_ID, "admin_note", f"uid={note_uid}")
            await update.effective_chat.send_message(
                f"📝 *Note saved for* `{note_uid}`.",
                parse_mode=ParseMode.MARKDOWN,
                reply_markup=rkb_admin_back(),
            )
        return True

    if state == "ADMIN_WAIT_CAP":
        ctx.user_data.pop("state", None)
        try:
            cap = int(text.strip())
            if cap < 0:
                raise ValueError
        except ValueError:
            await update.effective_chat.send_message(
                "❌ Invalid cap. Send a non-negative integer (0 = no limit).",
                reply_markup=rkb_admin_back(),
            )
            return True
        set_account_cap(cap)
        await update.effective_chat.send_message(
            f"✅ Account cap set to `{'No limit' if not cap else cap}`.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_back(),
        )
        return True

    # Fall through to original handler
    return await _orig_handle_admin_message(update, ctx, uid, text, state)


# Monkey-patch so on_message uses the extended handler
_handle_admin_message = _handle_admin_message_v2


# ── Patch admin inline callback handler for new buttons ──────
_orig_handle_admin_callback = _handle_admin_callback  # noqa: F821 (defined earlier in file)

async def _handle_admin_callback_v2(q, ctx: ContextTypes.DEFAULT_TYPE, uid: int, data: str) -> bool:
    """Extended admin callback handler."""
    if uid != ADMIN_ID:
        return False

    if data.startswith("ADMIN_NOTE:"):
        target_uid = int(data.split(":", 1)[1])
        ctx.user_data["state"]          = "ADMIN_WAIT_NOTE"
        ctx.user_data["admin_note_uid"] = target_uid
        ctx.user_data["admin_mode"]     = True
        existing = db_get_admin_note(target_uid)
        note_info = f"\n_Current note: {existing}_" if existing else ""
        await q.message.reply_text(
            f"📝 *Add/Update Note for* `{target_uid}`{note_info}\n\nSend the note text.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_cancel(),
        )
        return True

    if data.startswith("ADMIN_FORCEUNLOCK:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_force_unlock(q, target_uid)
        return True

    if data.startswith("ADMIN_EXPORTUSER:"):
        target_uid = int(data.split(":", 1)[1])
        await _admin_export_user_data(q, target_uid)
        return True

    if data == "ADMIN_RT_MAINT_TOGGLE":
        new_val = not is_maintenance_mode()
        set_maintenance_mode(new_val)
        reg_locked = is_registration_locked()
        cap        = get_account_cap()
        try:
            await q.edit_message_reply_markup(
                reply_markup=ikb_runtime_settings(new_val, reg_locked, cap)
            )
        except (BadRequest, TelegramError):
            pass
        await q.message.reply_text(
            f"🚧 Maintenance mode: *{'ON' if new_val else 'OFF'}*",
            parse_mode=ParseMode.MARKDOWN,
        )
        return True

    if data == "ADMIN_RT_REG_TOGGLE":
        new_val = not is_registration_locked()
        set_registration_lock(new_val)
        maint = is_maintenance_mode()
        cap   = get_account_cap()
        try:
            await q.edit_message_reply_markup(
                reply_markup=ikb_runtime_settings(maint, new_val, cap)
            )
        except (BadRequest, TelegramError):
            pass
        await q.message.reply_text(
            f"🔒 Registration: *{'LOCKED' if new_val else 'OPEN'}*",
            parse_mode=ParseMode.MARKDOWN,
        )
        return True

    if data == "ADMIN_RT_CAP_SET":
        ctx.user_data["state"]      = "ADMIN_WAIT_CAP"
        ctx.user_data["admin_mode"] = True
        await q.message.reply_text(
            f"📦 *Set Account Cap*\n\n"
            f"Current: `{'No limit' if not get_account_cap() else get_account_cap()}`\n\n"
            "Send the new cap (number of max accounts per user, 0 = no limit).",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_admin_cancel(),
        )
        return True

    if data.startswith("ADMIN_SCHED_CANCEL:"):
        broadcast_id = data.split(":", 1)[1]
        task = _scheduled_broadcasts.pop(broadcast_id, None)
        if task and not task.done():
            task.cancel()
        db_cancel_scheduled_broadcast(broadcast_id)
        audit(ADMIN_ID, "admin_sched_cancel", broadcast_id[:8])
        await q.message.reply_text(
            f"❌ Scheduled broadcast `{broadcast_id[:8]}` cancelled.",
            parse_mode=ParseMode.MARKDOWN,
        )
        return True

    # Fall through to original
    return await _orig_handle_admin_callback(q, ctx, uid, data)


# Monkey-patch the admin callback handler
_handle_admin_callback = _handle_admin_callback_v2


# ── Upgrade /admin command to show v2 panel ──────────────────
@admin_only
async def cmd_admin_v2(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    ctx.user_data.clear()
    ctx.user_data["admin_mode"] = True
    stats = db_global_stats()
    maint_warn = "\n\n⚠️ *MAINTENANCE MODE IS ON*" if is_maintenance_mode() else ""
    reg_warn   = "\n🔒 *Registration LOCKED*" if is_registration_locked() else ""
    cap        = get_account_cap()
    cap_str    = f"\n📦 Account cap: `{cap}`" if cap else ""
    await update.message.reply_text(
        "🛡 *NexAuth Admin Panel v2*\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Users        : `{stats['total_users']}`  _(+{stats['new_users_24h']} today)_\n"
        f"🔐 Accounts     : `{stats['total_accounts']}`\n"
        f"🔓 Sessions     : `{stats['active_sessions']}`\n"
        f"🚫 Banned       : `{stats['banned_users']}`\n"
        f"🔔 Pending resets: `{stats['pending_resets']}`\n"
        f"📋 Actions 24h  : `{stats['audit_24h']}`\n"
        f"📋 Actions 7d   : `{stats['audit_7d']}`"
        + maint_warn + reg_warn + cap_str +
        "\n\nUse the panel below to manage the bot.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_admin_v2(),
    )


# ── Maintenance mode guard (inject into cmd_start / on_message)
async def _maintenance_guard(update: Update, uid: int) -> bool:
    """Returns True if user should be blocked due to maintenance mode."""
    if uid == ADMIN_ID:
        return False  # admin always allowed
    if is_maintenance_mode():
        try:
            await update.effective_chat.send_message(
                "🚧 *NexAuth is currently under maintenance.*\n\n"
                "We'll be back shortly. Thank you for your patience!",
                parse_mode=ParseMode.MARKDOWN,
            )
        except TelegramError:
            pass
        return True
    return False


# ── Registration lock guard ──────────────────────────────────
async def _registration_guard(update: Update, uid: int) -> bool:
    """Returns True if user tried to register but registration is locked."""
    if uid == ADMIN_ID:
        return False
    if is_registration_locked():
        existing = col_users.find_one({"uid": uid})
        if not existing:
            try:
                await update.effective_chat.send_message(
                    "🔒 *New registrations are temporarily closed.*\n\n"
                    "Please check back later.",
                    parse_mode=ParseMode.MARKDOWN,
                )
            except TelegramError:
                pass
            return True
    return False


# ── Account cap guard ────────────────────────────────────────
def _account_cap_guard(uid: int) -> bool:
    """Returns True if user has hit the account cap."""
    cap = get_account_cap()
    if not cap:
        return False
    count = col_accounts.count_documents({"uid": uid})
    return count >= cap


# ─────────────────────────────────────────────────────────────
# 26.  MAIN
# ─────────────────────────────────────────────────────────────
def main() -> None:
    global _bot_ref
    app = Application.builder().token(BOT_TOKEN).build()
    _bot_ref = app.bot

    app.add_handler(CommandHandler("start",        cmd_start))
    app.add_handler(CommandHandler("restart",      cmd_restart))
    app.add_handler(CommandHandler("help",         cmd_help))
    app.add_handler(CommandHandler("digest",       cmd_digest))
    app.add_handler(CommandHandler("broadcast",    cmd_broadcast))
    app.add_handler(CommandHandler("admin_stats",  cmd_admin_stats))
    # Use upgraded admin command
    app.add_handler(CommandHandler("admin",        cmd_admin_v2))
    app.add_handler(MessageHandler(
        filters.Regex(r"^/resetreview_") & filters.TEXT,
        cmd_resetreview,
    ))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.PHOTO, on_photo))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_message))
    app.add_error_handler(on_error)

    # Watchdog: cleanup-only pass every 10s (actual auto-lock is per-user via _auto_lock_user)
    app.job_queue.run_repeating(watchdog, interval=10, first=5)

    log.info("NexAuth v6 (Advanced Admin) started — polling.")
    app.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    main()
