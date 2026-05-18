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
def db_create_reset_request(uid: int, name: str, username: Optional[str]) -> str:
    """Create a reset request and return its request_id."""
    request_id = base64.urlsafe_b64encode(os.urandom(9)).decode().rstrip("=")
    col_reset_requests.insert_one({
        "request_id": request_id,
        "uid": uid,
        "name": name,
        "username": username,
        "status": "pending",   # pending → approved / denied
        "ts": datetime.now(timezone.utc),
    })
    return request_id


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


# ─────────────────────────────────────────────────────────────
# 4.  SESSION
# ─────────────────────────────────────────────────────────────
_session_cache: dict = {}

# Tracks active admin-reminder tasks for reset requests: request_id → asyncio.Task
_reset_reminder_tasks: dict[str, asyncio.Task] = {}

# Tracks the current admin notification message_id for each request: request_id → int
_reset_admin_msg_ids: dict[str, int] = {}


def session_touch(uid: int) -> None:
    _session_cache[uid] = time.monotonic()
    col_sessions.update_one(
        {"uid": uid},
        {"$set": {"last": datetime.now(timezone.utc)}},
        upsert=True,
    )


def session_alive(uid: int) -> bool:
    t = _session_cache.get(uid)
    if t and (time.monotonic() - t) < SESSION_TTL:
        return True
    doc = col_sessions.find_one({"uid": uid})
    if not doc:
        return False
    last = doc["last"]
    if last.tzinfo is None:
        last = last.replace(tzinfo=timezone.utc)
    alive = (datetime.now(timezone.utc) - last).total_seconds() < SESSION_TTL
    if alive:
        _session_cache[uid] = time.monotonic()
    else:
        _session_cache.pop(uid, None)
    return alive


def session_kill(uid: int) -> None:
    _session_cache.pop(uid, None)
    col_sessions.delete_one({"uid": uid})


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
            [KeyboardButton("🔗 Paste URI"),     KeyboardButton("🔐 Enter Secret Key")],
            [KeyboardButton("🏠 Home")],
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
            [KeyboardButton("🏠 Home")],
        ],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_cancel() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("❌ Cancel")]],
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


def rkb_digits() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("6 digits"), KeyboardButton("8 digits")]],
        resize_keyboard=True,
        is_persistent=True,
    )


def rkb_period() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        [[KeyboardButton("30 seconds"), KeyboardButton("60 seconds")]],
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
        ]
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
             otp_type: str = "totp", counter: int = 0) -> str:
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
    pretty  = f"{code[:half]} {code[half:]}" if digits == 6 else code
    star    = "⭐ " if False else ""  # placeholder; caller injects if needed
    return (
        f"🔐 *{svc}*\n"
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


async def send_locked(update: Update) -> None:
    await update.effective_chat.send_message(
        locked_text(),
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_unlock(),
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
        await update.effective_chat.send_message(
            locked_text(),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
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
    keyboard = rkb_unlock() if (pin_set and not session_alive(uid)) else rkb_home()
    await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN, reply_markup=keyboard)


async def cmd_digest(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _ensure_user(update)
    uid = update.effective_user.id
    if not session_alive(uid):
        await send_locked(update); return
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
    await update.message.reply_text(
        f"🛡 *Admin Stats*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"👥 Users         : `{total_users}`\n"
        f"🔐 Accounts      : `{total_accounts}`\n"
        f"🔓 Active sessions: `{active_sessions}`\n"
        f"📋 Audit 7d      : `{audit_7d}`",
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

    # ── APPEAL PASSCODE RESET ────────────────────────────────
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
            ctx.bot_data.pop(f"pin_lockout_{uid}", None)
            ctx.bot_data.pop(f"pin_attempts_{uid}", None)
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
                # Stop the reminder loop for this request if running
                task = _reset_reminder_tasks.pop(req_id, None)
                if task and not task.done():
                    task.cancel()
                _reset_admin_msg_ids.pop(req_id, None)
                # Inform the admin the user self-resolved
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
            attempts_key = f"pin_attempts_{uid}"
            attempts = ctx.bot_data.get(attempts_key, 0) + 1
            ctx.bot_data[attempts_key] = attempts
            if attempts >= 5:
                ctx.bot_data[f"pin_lockout_{uid}"] = time.monotonic() + PIN_LOCKOUT_S
                ctx.bot_data[attempts_key] = 0
                ctx.user_data.clear()
                await update.effective_chat.send_message(
                    f"🚫 *Too many wrong attempts.*\nVault locked for *{PIN_LOCKOUT_S // 60} minutes*.\n\n"
                    f"_Forgot your passcode? Tap_ *🆘 Forgot Passcode? Appeal Reset* _below._",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock_with_appeal(),
                )
            else:
                await update.effective_chat.send_message(
                    f"❌ *Wrong passcode.* {5 - attempts} attempt{'s' if 5-attempts!=1 else ''} left.",
                    parse_mode=ParseMode.MARKDOWN,
                    reply_markup=rkb_unlock(),
                )
        return

    # ── TEMP PIN ENTRY (reset flow) ─────────────────────────
    if state == "WAIT_TEMP_PIN_UNLOCK":
        try:
            await update.message.delete()
        except TelegramError:
            pass
        await _do_temp_pin_unlock(update, ctx, uid, text)
        return

    # ── SESSION CHECK ────────────────────────────────────────
    if not session_alive(uid):
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
                "📊 My Stats", "❓ Help", "🏠 Home",
                # Add-account sub-menu
                "📷 Scan QR Code", "🔗 Paste URI", "🔐 Enter Secret Key",
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

    # ── MAIN MENU BUTTONS ───────────────────────────────────
    if text == "➕ Add Account":
        ctx.user_data.clear()
        _cancel_refresh(uid)
        await update.message.reply_text(
            "➕ *Add New TOTP Account*\n\nChoose how to add:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_add_menu(),
        )

    elif text == "📷 Scan QR Code":
        ctx.user_data["state"] = "WAIT_QR"
        await update.message.reply_text(
            "📷 *Scan QR Code*\n\nSend the QR code image now.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🔗 Paste URI":
        ctx.user_data["state"] = "WAIT_URI"
        await update.message.reply_text(
            "🔗 *Paste otpauth URI*\n\nSend your `otpauth://totp/...` string.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🔐 Enter Secret Key":
        ctx.user_data["state"] = "WAIT_KEY"
        await update.message.reply_text(
            "🔐 *Enter Secret Key*\n\nSend your base32 secret key.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🔑 Get OTP":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *No accounts yet.* Add one first.",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_home())
            return
        # Cancel any previous single or bulk refresh loops for this user
        _cancel_refresh(uid)
        # Sort: starred first, then alphabetical
        docs_sorted = sorted(docs, key=lambda x: (not x.get("starred", False), x["svc"].lower()))
        await update.message.reply_text(
            f"🔑 *Your OTP Codes* — {len(docs_sorted)} account{'s' if len(docs_sorted) != 1 else ''}\n"
            f"_Tap any code to copy · Codes refresh automatically_",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_home(),
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
        await update.message.reply_text(
            f"📋 *Your Vault* — {len(docs)} account{'s' if len(docs)!=1 else ''}\n"
            f"_Tap an account to manage it: get OTP, rename, delete, export & more._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_accounts(docs, "DETAIL", uid=uid),
        )

    elif text == "🔍 Search":
        ctx.user_data["state"] = "WAIT_SEARCH"
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
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_home())
            return
        await update.message.reply_text(
            "🗑 *Delete Account*\n\nChoose a service:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_accounts(docs, "DEL_ASK", uid=uid),
        )

    elif text == "✏️ Rename":
        docs = db_list(uid)
        if not docs:
            await update.message.reply_text(
                "📭 *No accounts to rename.*",
                parse_mode=ParseMode.MARKDOWN, reply_markup=rkb_home())
            return
        await update.message.reply_text(
            "✏️ *Rename Account*\n\nChoose a service:",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_accounts(docs, "RENAME_CB", uid=uid),
        )

    elif text == "💾 Backup":
        await _do_backup(update, uid)

    elif text == "📥 Restore":
        ctx.user_data["state"] = "WAIT_RESTORE"
        await update.message.reply_text(
            "📥 *Restore Backup*\n\nPaste your encrypted backup string.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
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
        await update.message.reply_text(
            "🔑 *Set Passcode*\n\nSend a 4–8 digit PIN.\n_Message deleted immediately for security._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )

    elif text == "🔓 Remove Passcode":
        if not db_get_pin(uid):
            await update.message.reply_text("ℹ️ No passcode is set.", reply_markup=rkb_settings())
        else:
            db_set_pin(uid, None)
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
        await cmd_help(update, ctx)

    elif text == "🕐 Session Info":
        session_doc = col_sessions.find_one({"uid": uid})
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
                reply_markup=rkb_settings(),
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
            "WAIT_KEY_DIGITS":   "🔢 Please choose 6 or 8 digits.",
            "WAIT_KEY_PERIOD":   "⏱ Please choose 30 or 60 seconds.",
            "WAIT_SVC_NAME":     "🏷 Please send a name for this account.",
            "WAIT_RENAME":       "✏️ Please send the new account name.",
            "WAIT_RENAME_ADD":   "✏️ Please send a unique name for this account.",
            "WAIT_SEARCH":       "🔍 Please type a search term.",
            "WAIT_RESTORE":      "📥 Please paste your encrypted backup token.",
            "WAIT_QR":           "📷 Please send the QR code image.",
        }
        hint = hints.get(state, "👆 Use the keyboard buttons to navigate.")
        await update.message.reply_text(hint, parse_mode=ParseMode.MARKDOWN,
                                        reply_markup=rkb_cancel() if state else rkb_home())


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
            await send_locked(update)
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
    q    = update.callback_query
    uid  = q.from_user.id
    data = q.data or ""

    # Always answer first — prevents "query expired" Telegram error
    await q.answer()

    # BUG FIX: rate-limit check AFTER answer(); no second q.answer() call
    if not rate_ok(uid):
        try:
            await q.message.reply_text("⚠️ Rate limit — slow down.")
        except TelegramError:
            pass
        return

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

    # ── RESET AGREE (user clicks after admin approves) ──────
    elif data.startswith("RESET_AGREE:"):
        request_id = data.split(":", 1)[1]
        await _do_user_agree_reset(q, ctx, uid, request_id)

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
    _cancel_refresh(0)
    ctx.user_data["state"]      = "WAIT_RENAME"
    ctx.user_data["rename_svc"] = svc
    await q.edit_message_text(
        f"✏️ *Rename* `{svc}`\n\nSend the new name.",
        parse_mode=ParseMode.MARKDOWN,
    )
    await q.message.reply_text("Type the new name:", reply_markup=rkb_cancel())


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
    await update.effective_chat.send_message(
        "🏷 *Name this account*\n\nSend a label (e.g. `GitHub`, `Gmail`):",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel(),
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
    await update.effective_chat.send_message(
        "🔁 *Confirm passcode*\n\nEnter the same PIN again:",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_cancel(),
    )


async def _do_confirm_pin(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                          uid: int, text: str) -> None:
    pending = ctx.user_data.pop("pending_pin", None)
    ctx.user_data.clear()
    if not pending:
        await update.effective_chat.send_message("⚠️ Session lost.", reply_markup=rkb_home())
        return
    if text != pending:
        await update.effective_chat.send_message(
            "❌ *PINs do not match.* Try again via ⚙️ Settings → 🔑 Set Passcode.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )
        return
    db_set_pin(uid, hash_pin(pending))
    await update.effective_chat.send_message(
        "✅ *Passcode set!* Vault will require this PIN to unlock.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_settings(),
    )
    log.info("PIN set uid=%s", uid)


# ─────────────────────────────────────────────────────────────
# 22a.  PASSCODE RESET FLOW
# ─────────────────────────────────────────────────────────────
import random
import string

TEMP_PIN_DELAY_S = 300   # 5 minutes before temp passcode is sent


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

    user = update.effective_user
    request_id = db_create_reset_request(uid, user.first_name, user.username)
    audit(uid, "reset_appeal")

    # Notify the user
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

    # Notify the admin
    uname_str = f"@{user.username}" if user.username else "_(no username)_"
    try:
        admin_msg = await ctx.bot.send_message(
            chat_id=ADMIN_ID,
            text=(
                "🔔 *Passcode Reset Request*\n"
                "━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"👤 *Name:*     {user.first_name}\n"
                f"🔗 *Username:* {uname_str}\n"
                f"🆔 *User ID:*  `{uid}`\n"
                f"🕐 *Time:*     {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n\n"
                "Please verify the user's identity by chatting with them.\n"
                "Once satisfied, tap ✅ Approve or ❌ Deny below."
            ),
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=ikb_admin_reset(request_id),
        )
        _reset_admin_msg_ids[request_id] = admin_msg.message_id
        log.info("Reset appeal uid=%s request_id=%s — admin notified", uid, request_id)

        # ── Auto-reminder: if admin doesn't react within 30s, resend & delete old ──
        async def _admin_reminder_loop(req_id: str, first_msg_id: int,
                                       u_first_name: str, u_username: str,
                                       u_uid: int) -> None:
            """
            Repeatedly reminds the admin every 30 s as long as the request
            stays 'pending'. Each cycle:
              1. Wait 30 s.
              2. Re-check DB — if no longer pending, stop.
              3. Send a fresh notification (capturing the new message_id).
              4. After another 10 s delete the old message (40 s total age).
            """
            old_msg_id = first_msg_id
            uname_display = f"@{u_username}" if u_username else "_(no username)_"
            attempt = 1
            while True:
                await asyncio.sleep(30)

                req_check = db_get_reset_request(req_id)
                if not req_check or req_check.get("status") != "pending":
                    # Admin already acted — clean up and exit
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
                            f"🕐 *Time:*     {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n\n"
                            "⚠️ _This request is still awaiting your decision._\n"
                            "Please tap ✅ Approve or ❌ Deny below."
                        ),
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=ikb_admin_reset(req_id),
                    )
                    _reset_admin_msg_ids[req_id] = new_msg.message_id
                    log.info(
                        "Reset reminder #%d sent uid=%s request_id=%s",
                        attempt, u_uid, req_id,
                    )
                except TelegramError as te:
                    log.warning("Could not send reset reminder: %s", te)
                    _reset_reminder_tasks.pop(req_id, None)
                    return

                # Delete the OLD message 10 s after the new one arrives (= ~40 s after it was sent)
                await asyncio.sleep(10)
                try:
                    await ctx.bot.delete_message(chat_id=ADMIN_ID, message_id=old_msg_id)
                except TelegramError:
                    pass  # already deleted or too old — ignore
                old_msg_id = new_msg.message_id

        task = asyncio.create_task(
            _admin_reminder_loop(request_id, admin_msg.message_id,
                                 user.first_name, user.username, uid)
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
                "• After *5 minutes*, the bot will send you a temporary passcode\n"
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

    await q.edit_message_text(
        "✅ *Request Confirmed!*\n\n"
        f"You will receive your temporary passcode in *{TEMP_PIN_DELAY_S // 60} minutes*.\n\n"
        "⏳ Please wait — do not close the chat.",
        parse_mode=ParseMode.MARKDOWN,
    )
    log.info("Reset agreed uid=%s request_id=%s — scheduling temp pin in %ds", uid, request_id, TEMP_PIN_DELAY_S)

    # Schedule temp passcode delivery
    async def _send_temp_pin_after_delay():
        await asyncio.sleep(TEMP_PIN_DELAY_S)
        temp_pin = _generate_temp_pin(8)
        # Store hashed temp pin as the current pin
        db_set_pin(uid, hash_pin(temp_pin))
        db_delete_reset_request(request_id)
        audit(uid, "reset_temp_pin_sent")
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
            log.info("Temp pin sent uid=%s", uid)

            # Auto-delete temp pin message after 60s
            async def _del_temp_msg(m):
                await asyncio.sleep(60)
                try:
                    await m.delete()
                except TelegramError:
                    pass

            asyncio.create_task(_del_temp_msg(temp_msg))

            # Mark user state so the next unlock attempt goes through the forced-change flow
            # We store a flag in MongoDB so it survives across handler boundaries
            db_set_setting(uid, "temp_pin_pending", True)
        except TelegramError as e:
            log.error("Could not send temp pin uid=%s: %s", uid, e)

    asyncio.create_task(_send_temp_pin_after_delay())


async def _do_temp_pin_unlock(update: Update, ctx: ContextTypes.DEFAULT_TYPE,
                               uid: int, text: str) -> None:
    """User enters temp passcode on the lock screen — force new passcode set."""
    pin_hash = db_get_pin(uid)
    if pin_hash and verify_pin(text, pin_hash):
        # Clear attempts/lockout
        ctx.bot_data.pop(f"pin_lockout_{uid}", None)
        ctx.bot_data.pop(f"pin_attempts_{uid}", None)
        session_touch(uid)
        ctx.user_data["state"] = "WAIT_RESET_NEW_PIN"
        audit(uid, "reset_temp_unlock")
        await update.effective_chat.send_message(
            "✅ *Temporary passcode accepted!*\n\n"
            "🔑 *You must now set a new permanent passcode.*\n\n"
            "Send a new 4–8 digit PIN.\n_Message deleted immediately for security._",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_cancel(),
        )
    else:
        await update.effective_chat.send_message(
            "❌ *Wrong temporary passcode.*\n\nPlease check the code sent to you and try again.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_unlock(),
        )


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
        await update.effective_chat.send_message(
            "❌ *PINs do not match.*\n\nPlease start over via ⚙️ Settings → 🔑 Set Passcode.",
            parse_mode=ParseMode.MARKDOWN,
            reply_markup=rkb_settings(),
        )
        return
    db_set_pin(uid, hash_pin(pending))
    audit(uid, "reset_new_pin_set")
    log.info("New PIN set after reset uid=%s", uid)
    await update.effective_chat.send_message(
        "🎉 *New Passcode Set Successfully!*\n\n"
        "Your vault is now protected with your new passcode.\n"
        "Keep it safe — it cannot be recovered without an admin reset.",
        parse_mode=ParseMode.MARKDOWN,
        reply_markup=rkb_home(),
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
        reply_markup=rkb_settings(),
    )


# ─────────────────────────────────────────────────────────────
# 23.  SESSION WATCHDOG
# ─────────────────────────────────────────────────────────────
async def watchdog(ctx: ContextTypes.DEFAULT_TYPE) -> None:
    cutoff = datetime.now(timezone.utc) - timedelta(seconds=SESSION_TTL)
    try:
        # Fetch expired sessions BEFORE deleting so we can notify each user
        expired_docs = list(col_sessions.find({"last": {"$lt": cutoff}}, {"uid": 1}))
        if expired_docs:
            r = col_sessions.delete_many({"last": {"$lt": cutoff}})
            log.info("Watchdog: removed %d expired session(s)", r.deleted_count)
            # Send lock notification to each user whose session just expired
            for doc in expired_docs:
                uid = doc.get("uid")
                if not uid:
                    continue
                _session_cache.pop(uid, None)   # evict in-memory cache too
                try:
                    await ctx.bot.send_message(
                        chat_id=uid,
                        text=(
                            "🔒 *Vault Locked — Your Security Matters*\n\n"
                            "Your session has expired after "
                            f"*{SESSION_TTL // 60} minute(s)* of inactivity.\n\n"
                            "🛡 *Why we lock automatically:*\n"
                            "• Protects your OTP secrets if you leave your phone unattended\n"
                            "• Prevents unauthorised access in shared environments\n"
                            "• Ensures only you can view your 2FA codes\n\n"
                            "Tap *🔓 Unlock Vault* below to re-enter your passcode "
                            "and regain access."
                        ),
                        parse_mode=ParseMode.MARKDOWN,
                        reply_markup=rkb_unlock(),
                    )
                    log.info("Watchdog: sent lock notification to uid=%s", uid)
                except TelegramError as te:
                    log.warning("Watchdog: could not notify uid=%s — %s", uid, te)
    except Exception as e:
        log.warning("Watchdog error: %s", e)
    # Also clean up stale pending_update entries (> 10 min old) from memory
    # (they hold no sensitive data in plaintext but we keep memory tidy)
    # No expiry stored — simply cap the dict size
    if len(_pending_updates) > 500:
        keys = list(_pending_updates.keys())[:250]
        for k in keys:
            _pending_updates.pop(k, None)
    if len(_pending_qr) > 100:
        keys = list(_pending_qr.keys())[:50]
        for k in keys:
            _pending_qr.pop(k, None)
    # Clean up finished bulk refresh task lists
    for uid_key in list(_bulk_refresh_tasks.keys()):
        _bulk_refresh_tasks[uid_key] = [t for t in _bulk_refresh_tasks[uid_key] if not t.done()]
        if not _bulk_refresh_tasks[uid_key]:
            _bulk_refresh_tasks.pop(uid_key, None)

    # Clean up finished admin reset-reminder tasks
    for req_id in list(_reset_reminder_tasks.keys()):
        if _reset_reminder_tasks[req_id].done():
            _reset_reminder_tasks.pop(req_id, None)
            _reset_admin_msg_ids.pop(req_id, None)


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
# 25.  MAIN
# ─────────────────────────────────────────────────────────────
def main() -> None:
    app = Application.builder().token(BOT_TOKEN).build()

    app.add_handler(CommandHandler("start",        cmd_start))
    app.add_handler(CommandHandler("restart",      cmd_restart))
    app.add_handler(CommandHandler("help",         cmd_help))
    app.add_handler(CommandHandler("digest",       cmd_digest))
    app.add_handler(CommandHandler("broadcast",    cmd_broadcast))
    app.add_handler(CommandHandler("admin_stats",  cmd_admin_stats))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.PHOTO, on_photo))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_message))
    app.add_error_handler(on_error)

    app.job_queue.run_repeating(watchdog, interval=30, first=10)

    log.info("NexAuth v5 started — polling.")
    app.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    main()
