#!/usr/bin/env python3
"""
WizStreamBot - Wizard101 level/school reader for streaming.

Web-based control panel at http://127.0.0.1:8765/ with:
  /              Full dashboard: setup, start/stop, settings, log
  /overlay       Transparent OBS browser source (compact school + level)
  /api/status    JSON API
  /api/config    Settings GET/POST
  /api/control   POST: start | stop | read_once | shutdown

Installation:
  pip install pillow
  Install Tesseract OCR from: https://github.com/UB-Mannheim/tesseract/wiki

Usage:
  python WizStreamBot.py              Start with web server and open dashboard
  python WizStreamBot.py --no-browser Start web server without opening browser
  python WizStreamBot.py --port 8770  Use different port
  python WizStreamBot.py test         Single read test
  python WizStreamBot.py band         Save levelup_band.png to check the scan area
  python WizStreamBot.py listen       Live level-up meter (tune the gate value)

Level-up detection:
  The character sheet is only read when it is on screen, so the level would
  otherwise go stale until the next sheet read. Two watchers close that gap:

  Screen  - watches the middle of the game window for the magenta LEVEL UP
            banner, confirms it with OCR, then adds one level.
  Sound   - optional. Learn the level-up jingle once from the dashboard, then
            it fires on the sound alone (useful when the banner is covered by
            dialogue). Needs: pip install sounddevice numpy

  Either watcher adds one level. The next real sheet read overrides whatever
  they counted, so a miscount never sticks.
"""

import argparse
import ctypes
import difflib
import io
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
import urllib.request
import webbrowser
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse, parse_qs

# ============================================================================
# CONFIG
# ============================================================================

IS_WINDOWS = os.name == "nt"
APP_VERSION = "3.0.0"
DEFAULT_PORT = 8765

SCHOOLS = ["Pyromancer", "Thaumaturge", "Diviner", "Theurgist",
           "Necromancer", "Conjurer", "Sorcerer"]

ELEMENTS = {
    "Pyromancer": "Fire", "Thaumaturge": "Ice", "Diviner": "Storm",
    "Theurgist": "Life", "Necromancer": "Death", "Conjurer": "Myth",
    "Sorcerer": "Balance",
}

ELEMENT_COLORS = {
    "Fire": "#ff6a2a", "Ice": "#5fd0ff", "Storm": "#a86bff",
    "Life": "#57d98a", "Death": "#9d8fb5", "Myth": "#ffd447",
    "Balance": "#e6c07a",
}

SCHOOL_ALIASES = {
    "PYROMANCER": "Pyromancer", "FIRE": "Pyromancer",
    "THAUMATURGE": "Thaumaturge", "ICE": "Thaumaturge",
    "DIVINER": "Diviner", "DIVINE": "Diviner", "STORM": "Diviner",
    "THEURGIST": "Theurgist", "LIFE": "Theurgist",
    "NECROMANCER": "Necromancer", "DEATH": "Necromancer",
    "CONJURER": "Conjurer", "MYTH": "Conjurer",
    "SORCERER": "Sorcerer", "BALANCE": "Sorcerer",
}

RANKS = [
    (1, 4, "Novice"), (5, 9, "Apprentice"), (10, 14, "Initiate"),
    (15, 19, "Journeyman"), (20, 29, "Adept"), (30, 39, "Magus"),
    (40, 49, "Master"), (50, 59, "Grandmaster"), (60, 69, "Legendary"),
    (70, 79, "Transcendent"), (80, 89, "Archmage"), (90, 99, "Promethean"),
    (100, 109, "Exalted"), (110, 119, "Prodigious"), (120, 129, "Champion"),
    (130, 139, "Visionary"), (140, 149, "Cosmic"), (150, 159, "Paragon"),
    (160, 169, "Prime"), (170, 170, "Supreme"),
]

CHAR_TITLE = (0.245, 0.038, 0.510, 0.090)  # Character screen title
GAME_TITLE = (0.075, 0.055, 0.410, 0.205)  # In-game sheet title

TESSERACT_GUESSES = [
    r"C:\Program Files\Tesseract-OCR\tesseract.exe",
    r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
    "/usr/bin/tesseract", "/opt/homebrew/bin/tesseract",
]

# ============================================================================
# HELPERS
# ============================================================================

def element_name(school):
    """Pyromancer -> Fire, Thaumaturge -> Ice, etc."""
    if not school:
        return ""
    if school in ELEMENTS:
        return ELEMENTS[school]
    title = str(school).strip().title()
    if title in ELEMENTS:
        return ELEMENTS[title]
    for elem in ELEMENTS.values():
        if elem.lower() == title.lower():
            return elem
    return str(school)


def rank_for_level(level):
    if level is None:
        return None
    for lo, hi, rank in RANKS:
        if lo <= level <= hi:
            return rank
    return None


def normalize_text(text):
    text = text.upper().replace("|", "I").replace("\u2014", "-")
    return " ".join(re.sub(r"[^A-Z0-9]+", " ", text).split())


def find_level(text, cfg):
    raw = normalize_text(text)
    lo = int(cfg.get("min_level", 1))
    hi = int(cfg.get("max_level", 180))
    for pattern in (r"LEVEL\s*([0-9]{1,3})", r"LEV(?:EL|EI|E1|E)\s*([0-9]{1,3})"):
        m = re.search(pattern, raw)
        if m:
            n = int(m.group(1))
            if lo <= n <= hi:
                return n
    candidates = [int(s) for s in re.findall(r"\b([0-9]{1,3})\b", raw)
                  if lo <= int(s) <= hi]
    if len(candidates) == 1:
        return candidates[0]
    idx = raw.find("LEVEL")
    if idx >= 0:
        nums = re.findall(r"\b([0-9]{1,3})\b", raw[idx:idx + 30])
        if nums and lo <= int(nums[0]) <= hi:
            return int(nums[0])
    return None


def school_from_text(text):
    raw = normalize_text(text)
    compact = raw.replace(" ", "")
    tokens = set(raw.split())
    for alias, school in SCHOOL_ALIASES.items():
        if alias in tokens:
            return school
        if len(alias) >= 5 and alias in compact:
            return school
    best_school, best_score = None, 0.0
    for school in SCHOOLS:
        target = school.upper()
        score = difflib.SequenceMatcher(None, compact, target).ratio()
        for token in raw.split():
            score = max(score, difflib.SequenceMatcher(None, token, target).ratio())
        if score > best_score:
            best_school, best_score = school, score
    return best_school if best_score >= 0.78 else None


# ============================================================================
# LOGGING
# ============================================================================

LOG_LOCK = threading.Lock()
LOG_BUFFER = deque(maxlen=500)


def log(msg, level="info"):
    stamp = time.strftime("%H:%M:%S")
    with LOG_LOCK:
        LOG_BUFFER.append({"time": stamp, "level": level, "text": str(msg)})
    print(f"[{stamp}] {msg}")


def get_logs():
    with LOG_LOCK:
        return list(LOG_BUFFER)


def clear_logs():
    with LOG_LOCK:
        LOG_BUFFER.clear()


# ============================================================================
# WINDOWS - find Wizard101 window
# ============================================================================

if IS_WINDOWS:
    from ctypes import wintypes

    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    EnumWindowsProc = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)

    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel32.CloseHandle.restype = wintypes.BOOL
    kernel32.QueryFullProcessImageNameW.argtypes = [
        wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR,
        ctypes.POINTER(wintypes.DWORD)]
    kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL

    user32.GetForegroundWindow.argtypes = []
    user32.GetForegroundWindow.restype = wintypes.HWND
    user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    user32.GetWindowTextLengthW.argtypes = [wintypes.HWND]
    user32.GetWindowTextLengthW.restype = ctypes.c_int
    user32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowTextW.restype = ctypes.c_int
    user32.IsWindowVisible.argtypes = [wintypes.HWND]
    user32.IsWindowVisible.restype = wintypes.BOOL
    user32.GetClientRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
    user32.GetClientRect.restype = wintypes.BOOL
    user32.ClientToScreen.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.POINT)]
    user32.ClientToScreen.restype = wintypes.BOOL
    user32.EnumWindows.argtypes = [EnumWindowsProc, wintypes.LPARAM]
    user32.EnumWindows.restype = wintypes.BOOL

    def enable_dpi_awareness():
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(2)
        except:
            pass
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except:
            pass

    def get_process_name(pid):
        if not pid:
            return ""
        handle = kernel32.OpenProcess(0x1000, False, pid)
        if not handle:
            return ""
        try:
            buf = ctypes.create_unicode_buffer(1024)
            size = wintypes.DWORD(len(buf))
            if kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                return os.path.basename(buf.value)
        finally:
            kernel32.CloseHandle(handle)
        return ""

    def get_window_process(hwnd):
        pid = wintypes.DWORD()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        return pid.value, get_process_name(pid.value)

    def get_window_title(hwnd):
        length = user32.GetWindowTextLengthW(hwnd)
        if length <= 0:
            return ""
        buf = ctypes.create_unicode_buffer(length + 1)
        user32.GetWindowTextW(hwnd, buf, length + 1)
        return buf.value

    def get_client_rect_screen(hwnd):
        rect = wintypes.RECT()
        if not user32.GetClientRect(hwnd, ctypes.byref(rect)):
            return None
        pt = wintypes.POINT(0, 0)
        if not user32.ClientToScreen(hwnd, ctypes.byref(pt)):
            return None
        w = rect.right - rect.left
        h = rect.bottom - rect.top
        if w <= 0 or h <= 0:
            return None
        return pt.x, pt.y, w, h

    def find_game_window(cfg):
        wanted = str(cfg.get("trigger_process", "WizardGraphicalClient.exe")).lower()
        hint = str(cfg.get("window_title_hint", "Wizard101")).lower()

        def matches(hwnd):
            _pid, proc = get_window_process(hwnd)
            if proc:
                return proc.lower() == wanted
            title = get_window_title(hwnd)
            return bool(title) and hint in title.lower()

        fg = user32.GetForegroundWindow()
        if fg and matches(fg) and user32.IsWindowVisible(fg):
            client = get_client_rect_screen(fg)
            if client:
                return {"hwnd": fg, "client": client, "title": get_window_title(fg)}

        found = []
        def callback(hwnd, _):
            if not user32.IsWindowVisible(hwnd) or not matches(hwnd):
                return True
            client = get_client_rect_screen(hwnd)
            if client:
                found.append({"hwnd": hwnd, "client": client, "title": get_window_title(hwnd)})
            return True

        user32.EnumWindows(EnumWindowsProc(callback), 0)
        if not found:
            return None
        found.sort(key=lambda x: (hint not in x["title"].lower(),
                                  -x["client"][2] * x["client"][3]))
        return found[0]
else:
    def enable_dpi_awareness():
        pass

    def find_game_window(cfg):
        return None


# ============================================================================
# IMAGE CAPTURE & MASKS
# ============================================================================

def grab_region(client, box):
    from PIL import ImageGrab
    left, top, cw, ch = client
    x, y, w, h = box
    l = int(left + x * cw)
    t = int(top + y * ch)
    r = l + max(1, int(w * cw))
    b = t + max(1, int(h * ch))
    return ImageGrab.grab(bbox=(l, t, r, b), all_screens=True).convert("RGB")


def _gt(band, value):
    return band.point([255 if i > value else 0 for i in range(256)])


def _lt(band, value):
    return band.point([255 if i < value else 0 for i in range(256)])


def _gt_scaled(a, b, factor):
    from PIL import ImageChops
    scaled = b.point([min(255, int(i * factor)) for i in range(256)])
    return _gt(ImageChops.subtract(a, scaled), 0)


def _all(*masks):
    from PIL import ImageChops
    out = masks[0]
    for m in masks[1:]:
        out = ImageChops.multiply(out, m)
    return out


def blue_mask(img):
    r, g, b = img.split()
    return _all(_gt(b, 105), _gt_scaled(b, r, 1.20), _gt_scaled(b, g, 1.03))


def gold_mask(img):
    r, g, b = img.split()
    return _all(_gt(r, 125), _gt(g, 85), _lt(b, 170), _gt_scaled(r, g, 0.88))


def _density(mask):
    hist = mask.histogram()
    total = float(max(1, sum(hist)))
    return sum(hist[128:]) / total


def blue_text_density(img):
    r, g, b = img.split()
    return _density(_all(_gt(b, 105), _gt_scaled(b, r, 1.25), _gt_scaled(b, g, 1.05)))


def gold_text_density(img):
    r, g, b = img.split()
    return _density(_all(_gt(r, 130), _gt(g, 90), _lt(b, 155), _gt_scaled(r, g, 0.90)))


def classify_screen(char_img, game_img):
    bd = blue_text_density(char_img)
    if bd >= 0.075:
        return "character"
    if gold_text_density(game_img) >= 0.18 and bd < 0.055:
        return "game"
    return "unknown"


def title_fingerprint(img):
    from PIL import ImageOps
    small = ImageOps.grayscale(img).resize((24, 8), resample=2)
    values = list(small.getdata())
    if not values:
        return None
    return tuple(v // 24 for v in values)


# ============================================================================
# OCR
# ============================================================================

_TESS_CACHE = {"path": None, "checked": False}


def find_tesseract(cfg):
    configured = str(cfg.get("tesseract_path", "")).strip()
    if configured and os.path.exists(configured):
        return configured
    if _TESS_CACHE["checked"]:
        return _TESS_CACHE["path"]
    _TESS_CACHE["checked"] = True
    for guess in TESSERACT_GUESSES:
        if os.path.exists(guess):
            _TESS_CACHE["path"] = guess
            return guess
    return None


def _no_window_kwargs():
    if not IS_WINDOWS:
        return {}
    startupinfo = subprocess.STARTUPINFO()
    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    startupinfo.wShowWindow = 0
    return {"startupinfo": startupinfo, "creationflags": 0x08000000}


def run_tesseract(exe, png_bytes, psm, timeout=8):
    proc = subprocess.Popen(
        [exe, "-", "-", "--psm", str(psm)],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        **_no_window_kwargs()
    )
    try:
        out, _err = proc.communicate(png_bytes, timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        return ""
    return out.decode("utf-8", "replace")


def prepare_ocr(img, mode, upscale):
    from PIL import ImageOps
    mask = blue_mask(img) if mode == "character" else gold_mask(img)
    scale = max(2, int(upscale))
    mask = mask.resize((mask.width * scale, mask.height * scale), resample=2)
    mask = ImageOps.expand(mask, border=12, fill=0)
    buf = io.BytesIO()
    mask.save(buf, format="PNG")
    return buf.getvalue()


def ocr_title(img, mode, cfg):
    exe = find_tesseract(cfg)
    if not exe:
        log("Tesseract not found - set path in settings or install it", level="warn")
        return {"level": None, "rank": None, "school": None}, ""
    png = prepare_ocr(img, mode, cfg.get("ocr_upscale", 3))
    texts = []
    for psm in (6, 11):
        text = run_tesseract(exe, png, psm)
        if text:
            texts.append(text)
        parsed = parse_title("\n".join(texts), cfg)
        if parsed["level"] is not None and parsed["school"] is not None:
            return parsed, "\n".join(texts)
    return parse_title("\n".join(texts), cfg), "\n".join(texts)


def parse_title(text, cfg):
    level = find_level(text, cfg)
    return {"level": level, "rank": rank_for_level(level),
            "school": school_from_text(text)}


def read_once(cfg):
    """One full capture + OCR cycle."""
    if not IS_WINDOWS:
        return None
    win = find_game_window(cfg)
    if not win:
        return None
    client = win["client"]
    char_img = grab_region(client, CHAR_TITLE)
    game_img = grab_region(client, GAME_TITLE)
    mode = classify_screen(char_img, game_img)
    if mode == "unknown":
        return None
    title_img = char_img if mode == "character" else game_img
    parsed, raw = ocr_title(title_img, mode, cfg)
    parsed["mode"] = mode
    parsed["raw"] = raw
    return parsed


# ============================================================================
# STATE & CONFIG
# ============================================================================

STATE_LOCK = threading.Lock()
STATE = {
    "running": False,
    "result": None,
    "reads": 0,
    "last_read": 0.0,

    # levels counted since the last real sheet read
    "bumps": 0,
    "levelup_at": 0.0,
    "levelup_source": "",
    "levelup_count": 0,
    "levelup_density": 0.0,
    "audio_score": 0.0,
    "audio_state": "off",
}

CFG = {
    "interval": 0.5,
    "idle_interval": 3.0,
    "ocr_refresh": 5.0,
    "ocr_upscale": 3,
    "min_level": 1,
    "max_level": 180,
    "tesseract_path": "",
    "trigger_process": "WizardGraphicalClient.exe",
    "window_title_hint": "Wizard101",
    "debug": False,

    # --- level-up detection ---
    "levelup_visual": True,        # watch the screen for the LEVEL UP banner
    "levelup_audio": False,        # also listen for the level-up jingle
    "levelup_band": "0.12,0.16,0.76,0.48",   # x,y,w,h of the scan area (0-1)
    "levelup_gate": 0.0012,        # magenta density that wakes the OCR check
    "levelup_cooldown": 10.0,      # seconds before another level can register
    "levelup_tick": 0.25,          # seconds between checks
    "levelup_audio_threshold": 0.72,
    "text_out_dir": "",            # optional folder for level.txt / school.txt
}

SHUTDOWN = threading.Event()


def get_config():
    return dict(CFG)


def set_config(values):
    global CFG
    for k in CFG:
        if k in values:
            CFG[k] = values[k]
    return get_config()


def get_state():
    with STATE_LOCK:
        result = dict(STATE["result"]) if STATE["result"] else None
        bumps = STATE["bumps"]
        snap = {
            "running": STATE["running"],
            "reads": STATE["reads"],
            "version": APP_VERSION,
            "bumps": bumps,
            "levelup_at": STATE["levelup_at"],
            "levelup_source": STATE["levelup_source"],
            "levelup_count": STATE["levelup_count"],
            "levelup_density": STATE["levelup_density"],
            "audio_score": STATE["audio_score"],
            "audio_state": STATE["audio_state"],
        }
    if result:
        base = result.get("level")
        level = base
        if base is not None and bumps:
            level = min(int(CFG.get("max_level", 180)), base + bumps)
        snap.update({
            "level": level,
            "base_level": base,
            "rank": rank_for_level(level) or result.get("rank"),
            "school": element_name(result.get("school")),
            "school_class": result.get("school"),
            "mode": result.get("mode"),
        })
    else:
        snap.update({"level": None, "base_level": None, "rank": None,
                     "school": "", "school_class": "", "mode": ""})
    return snap


def publish_result(result):
    """A real sheet read is authoritative - it clears any counted levels."""
    with STATE_LOCK:
        STATE["result"] = result
        STATE["reads"] += 1
        STATE["last_read"] = time.time()
        STATE["bumps"] = 0
    write_text_outputs()


# ============================================================================
# TEXT FILE OUTPUT (for OBS Text GDI+ sources)
# ============================================================================

def write_text_outputs():
    folder = str(CFG.get("text_out_dir", "")).strip()
    if not folder:
        return
    try:
        path = Path(folder)
        path.mkdir(parents=True, exist_ok=True)
        snap = get_state()
        level = snap.get("level")
        school = snap.get("school") or ""
        rank = snap.get("rank") or ""
        files = {
            "level.txt": "" if level is None else str(level),
            "school.txt": school,
            "rank.txt": rank,
            "status.txt": "" if level is None else f"Level {level} \u00b7 {school}".strip(" \u00b7"),
        }
        for name, text in files.items():
            (path / name).write_text(text, encoding="utf-8")
    except Exception as exc:
        log(f"could not write text files: {exc}", level="warn")


# ============================================================================
# LEVEL-UP DETECTION
# ============================================================================

LEVELUP_BAND_DEFAULT = (0.12, 0.16, 0.76, 0.48)
SOUND_FILE = Path(__file__).resolve().with_name("levelup_sound.json")


def parse_band(value):
    """'x,y,w,h' in 0-1 client fractions."""
    try:
        parts = [float(p) for p in str(value).replace(" ", "").split(",")]
        if len(parts) == 4 and all(0.0 <= p <= 1.0 for p in parts) and parts[2] > 0 and parts[3] > 0:
            return tuple(parts)
    except Exception:
        pass
    return LEVELUP_BAND_DEFAULT


def levelup_mask(img):
    """The LEVEL UP banner is magenta: red and blue both well above green."""
    r, g, b = img.split()
    return _all(_gt(r, 105), _gt(b, 105), _gt_scaled(r, g, 1.30), _gt_scaled(b, g, 1.30))


def levelup_density(img):
    return _density(levelup_mask(img))


def levelup_text_hit(text, threshold=0.55):
    """The banner font OCRs badly - '2FVEL UPPITY!' is a normal reading.
    Require an UP, then fuzzy-match the five characters in front of it."""
    compact = normalize_text(text).replace(" ", "")
    if "LEVELUP" in compact:
        return True, 1.0
    best = 0.0
    for match in re.finditer("UP", compact):
        prefix = compact[max(0, match.start() - 5):match.start()]
        if len(prefix) < 4:
            continue
        best = max(best, difflib.SequenceMatcher(None, prefix, "LEVEL").ratio())
    return best >= threshold, best


def confirm_levelup(img, cfg):
    """Second stage: OCR just the magenta pixels in the scan band."""
    from PIL import ImageOps
    exe = find_tesseract(cfg)
    if not exe:
        return False, "no tesseract"
    mask = levelup_mask(img)
    mask = mask.resize((mask.width * 3, mask.height * 3), resample=2)
    mask = ImageOps.expand(mask, border=16, fill=0)
    buf = io.BytesIO()
    mask.save(buf, format="PNG")
    png = buf.getvalue()
    texts = []
    for psm in (6, 11):
        text = run_tesseract(exe, png, psm, timeout=6)
        if text:
            texts.append(text)
            hit, score = levelup_text_hit(text)
            if hit:
                return True, " ".join("\n".join(texts).split())
    return False, " ".join("\n".join(texts).split())


def register_levelup(source, delta=1, force=False):
    """Add a level. Returns True if it counted."""
    now = time.time()
    cooldown = max(0.0, float(CFG.get("levelup_cooldown", 10.0)))
    with STATE_LOCK:
        if not force and delta > 0 and (now - STATE["levelup_at"]) < cooldown:
            return False
        if STATE["result"] is None and delta > 0:
            # nothing to add to yet - the sheet has never been read
            STATE["levelup_at"] = now
            return False
        STATE["bumps"] = max(-99, STATE["bumps"] + delta)
        if delta > 0:
            STATE["levelup_at"] = now
            STATE["levelup_source"] = source
            STATE["levelup_count"] += 1
    snap = get_state()
    if delta > 0:
        log(f"LEVEL UP ({source}) - now Level {snap.get('level')}")
    else:
        log(f"level corrected down - now Level {snap.get('level')}")
    write_text_outputs()
    return True


class AudioWatch:
    """Optional loopback listener that recognises the level-up jingle.

    Learns from whatever was playing a moment ago, so there is no need to
    ship an audio file: level up, then press Learn within a few seconds.
    """

    SR = 16000
    FRAME = 1024
    HOP = 512
    BANDS = 24
    BUFFER_SECONDS = 6.0

    def __init__(self):
        self.lock = threading.Lock()
        self.np = None
        self.sd = None
        self.stream = None
        self.error = ""
        self.device_sr = 48000
        self.decimate = 3
        self.ring = None
        self.write_at = 0
        self.edges = None
        self.window = None
        self.reference = None      # normalised (frames x BANDS) matrix
        self.ref_frames = 0
        self.load_reference()

    # ---- setup -----------------------------------------------------------
    def _imports(self):
        if self.np is None or self.sd is None:
            import numpy
            import sounddevice
            self.np = numpy
            self.sd = sounddevice

    def _prepare_math(self):
        np = self.np
        if self.window is None:
            self.window = np.hanning(self.FRAME).astype("float32")
        if self.edges is None:
            top = self.FRAME // 2
            raw = np.logspace(np.log10(4.0), np.log10(float(top)), self.BANDS + 1)
            self.edges = np.unique(raw.astype(int))
            if len(self.edges) < self.BANDS + 1:
                self.edges = np.linspace(4, top, self.BANDS + 1).astype(int)

    def ensure_started(self):
        if self.stream is not None:
            return True
        try:
            self._imports()
            self._prepare_math()
        except Exception as exc:
            self.error = f"needs 'pip install sounddevice numpy' ({exc})"
            self._set_state("missing")
            return False
        sd = self.sd
        np = self.np
        try:
            device, channels, extra = None, 2, None
            for index, api in enumerate(sd.query_hostapis()):
                if "wasapi" in str(api.get("name", "")).lower():
                    device = api.get("default_output_device")
                    if device is not None and device >= 0:
                        info = sd.query_devices(device)
                        channels = max(1, min(2, int(info.get("max_output_channels", 2)) or 2))
                        self.device_sr = int(info.get("default_samplerate", 48000))
                        extra = sd.WasapiSettings(loopback=True)
                    break
            if extra is None:
                info = sd.query_devices(kind="input")
                self.device_sr = int(info.get("default_samplerate", 48000))
                channels = 1
            self.decimate = max(1, int(round(self.device_sr / float(self.SR))))
            self.ring = np.zeros(int(self.SR * self.BUFFER_SECONDS), dtype="float32")
            self.write_at = 0
            self.stream = sd.InputStream(
                device=device, channels=channels, samplerate=self.device_sr,
                blocksize=2048, dtype="float32", callback=self._on_audio,
                extra_settings=extra)
            self.stream.start()
            self.error = ""
            self._set_state("listening")
            log("audio watcher started (loopback)")
            return True
        except Exception as exc:
            self.stream = None
            self.error = str(exc)
            self._set_state("error")
            log(f"audio watcher could not start: {exc}", level="warn")
            return False

    def ensure_stopped(self):
        if self.stream is None:
            return
        try:
            self.stream.stop()
            self.stream.close()
        except Exception:
            pass
        self.stream = None
        self._set_state("off")

    def _set_state(self, value):
        with STATE_LOCK:
            STATE["audio_state"] = value

    # ---- capture ---------------------------------------------------------
    def _on_audio(self, indata, _frames, _time, _status):
        try:
            np = self.np
            mono = indata.mean(axis=1) if indata.ndim > 1 else indata
            if self.decimate > 1:
                mono = mono[::self.decimate]
            chunk = np.asarray(mono, dtype="float32")
            with self.lock:
                size = len(self.ring)
                n = len(chunk)
                if n >= size:
                    self.ring[:] = chunk[-size:]
                    self.write_at = 0
                    return
                end = self.write_at + n
                if end <= size:
                    self.ring[self.write_at:end] = chunk
                else:
                    split = size - self.write_at
                    self.ring[self.write_at:] = chunk[:split]
                    self.ring[:n - split] = chunk[split:]
                self.write_at = end % size
        except Exception:
            pass

    def tail(self, samples):
        with self.lock:
            if self.ring is None:
                return None
            np = self.np
            size = len(self.ring)
            samples = min(samples, size)
            start = (self.write_at - samples) % size
            if start + samples <= size:
                return self.ring[start:start + samples].copy()
            return np.concatenate((self.ring[start:], self.ring[:(start + samples) % size]))

    # ---- fingerprint -----------------------------------------------------
    def _features(self, signal):
        """Log-band spectrogram, each frame unit length so loudness drops out."""
        np = self.np
        if signal is None or len(signal) < self.FRAME:
            return None
        count = 1 + (len(signal) - self.FRAME) // self.HOP
        if count < 1:
            return None
        index = (np.arange(self.FRAME)[None, :]
                 + self.HOP * np.arange(count)[:, None])
        spectrum = np.abs(np.fft.rfft(signal[index] * self.window, axis=1))
        spectrum = spectrum[:, :self.edges[-1]]
        sums = np.add.reduceat(spectrum, self.edges[:-1], axis=1)
        widths = np.diff(self.edges).astype("float32")
        out = np.log1p((sums / widths) * 40.0).astype("float32")
        # Centre each frame on its own mean. What survives is the shape of the
        # sound rather than its loudness or the level of whatever is under it,
        # which is what keeps game music from scoring.
        out = out - out.mean(axis=1, keepdims=True)
        norms = np.linalg.norm(out, axis=1, keepdims=True)
        norms[norms < 1e-6] = 1e-6
        return out / norms

    def learn(self, seconds=2.2):
        if not self.ensure_started():
            return False, self.error or "audio unavailable"
        np = self.np
        signal = self.tail(int(self.SR * seconds))
        if signal is None or len(signal) < self.FRAME * 2:
            return False, "not enough audio captured yet"
        if float(np.abs(signal).max()) < 0.005:
            return False, "that stretch of audio was silent"

        # Anchor on the loudest moment. The tail of a jingle is quiet and gets
        # swamped by game music, so the reference covers the onset instead.
        hops = 1 + (len(signal) - self.FRAME) // self.HOP
        energy = np.array([
            float(np.abs(signal[i * self.HOP:i * self.HOP + self.FRAME]).mean())
            for i in range(hops)])
        peak = int(energy.argmax())
        start = max(0, (peak - 3) * self.HOP)
        window = int(self.SR * 1.25)
        clip = signal[start:start + window]
        feats = self._features(clip)
        if feats is None or len(feats) < 8:
            return False, "not enough audio captured yet"
        self.reference = feats
        self.ref_frames = len(feats)
        try:
            SOUND_FILE.write_text(json.dumps({
                "sr": self.SR, "frame": self.FRAME, "hop": self.HOP,
                "bands": int(feats.shape[1]),
                "frames": [[round(float(v), 5) for v in row] for row in feats],
            }), encoding="utf-8")
        except Exception as exc:
            return True, f"learned, but could not save: {exc}"
        return True, f"learned {self.ref_frames} frames ({seconds:.1f}s)"

    def load_reference(self):
        if not SOUND_FILE.exists():
            return False
        try:
            self._imports()
            self._prepare_math()
            data = json.loads(SOUND_FILE.read_text(encoding="utf-8"))
            frames = data.get("frames") or []
            if not frames:
                return False
            self.reference = self.np.array(frames, dtype="float32")
            self.ref_frames = len(frames)
            return True
        except Exception:
            return False

    def poll(self, threshold):
        """Best score over several alignments, so the jingle can land anywhere
        between two polls and still be recognised."""
        if self.stream is None or self.reference is None or self.ref_frames < 8:
            return False
        np = self.np
        slack = 14                       # ~0.45s of alignment tolerance
        need = (self.ref_frames + slack) * self.HOP + self.FRAME
        feats = self._features(self.tail(need))
        if feats is None or len(feats) < self.ref_frames:
            return False
        target = self.reference.ravel()
        target_norm = float(np.linalg.norm(target))
        if target_norm < 1e-6:
            return False
        best = 0.0
        for offset in range(0, min(slack, len(feats) - self.ref_frames) + 1):
            end = len(feats) - offset
            current = feats[end - self.ref_frames:end].ravel()
            denom = float(np.linalg.norm(current)) * target_norm
            if denom < 1e-6:
                continue
            best = max(best, float(np.dot(current, target) / denom))
        with STATE_LOCK:
            STATE["audio_score"] = round(best, 4)
        return best >= threshold

    def status(self):
        if self.reference is None:
            return "no sound learned yet"
        if self.stream is None:
            return f"reference ready ({self.ref_frames} frames), not listening"
        return f"listening, reference {self.ref_frames} frames"


AUDIO = AudioWatch()


class LevelWatch(threading.Thread):
    """Fast, independent watcher - it does not share the reader's backoff."""

    def __init__(self):
        threading.Thread.__init__(self, name="WizStreamBotLevelWatch", daemon=True)
        self.wake = threading.Event()
        self.armed = True
        self.fails = 0
        self.last_confirm = 0.0
        self.win_at = 0.0
        self.win = None

    def _window(self, cfg):
        now = time.monotonic()
        if self.win and (now - self.win_at) < 4.0:
            return self.win
        self.win = find_game_window(cfg)
        self.win_at = now
        return self.win

    def run(self):
        while not SHUTDOWN.is_set():
            cfg = dict(CFG)
            tick = max(0.10, float(cfg.get("levelup_tick", 0.25)))
            visual = bool(cfg.get("levelup_visual", True))
            audio_on = bool(cfg.get("levelup_audio", False))
            with STATE_LOCK:
                running = STATE["running"]

            if not running or not IS_WINDOWS or not (visual or audio_on):
                if not running or not audio_on:
                    AUDIO.ensure_stopped()
                self.win = None
                self.wake.wait(0.6)
                self.wake.clear()
                continue

            try:
                if audio_on:
                    AUDIO.ensure_started()
                    if AUDIO.poll(float(cfg.get("levelup_audio_threshold", 0.72))):
                        register_levelup("sound")
                else:
                    AUDIO.ensure_stopped()

                if visual:
                    win = self._window(cfg)
                    if win:
                        img = grab_region(win["client"], parse_band(cfg.get("levelup_band")))
                        density = levelup_density(img)
                        with STATE_LOCK:
                            STATE["levelup_density"] = round(density, 5)
                        gate = float(cfg.get("levelup_gate", 0.0012))
                        now = time.monotonic()
                        if density >= gate:
                            if self.armed and (now - self.last_confirm) >= 0.7:
                                self.last_confirm = now
                                hit, raw = confirm_levelup(img, cfg)
                                if hit:
                                    register_levelup("screen")
                                    self.armed = False
                                    self.fails = 0
                                else:
                                    self.fails += 1
                                    if cfg.get("debug"):
                                        log(f"levelup gate open (density {density:.4f}) "
                                            f"but text was '{raw[:60]}'")
                                    if self.fails >= 3:
                                        self.armed = False
                        elif density < gate * 0.5:
                            self.armed = True
                            self.fails = 0
            except Exception as exc:
                log(f"level watch error: {exc}", level="warn")
                self.wake.wait(2.0)
                self.wake.clear()
                continue

            self.wake.wait(tick)
            self.wake.clear()


# ============================================================================
# READER THREAD
# ============================================================================

class Reader(threading.Thread):
    def __init__(self):
        threading.Thread.__init__(self, name="WizStreamBotReader", daemon=True)
        self.wake = threading.Event()

    def run(self):
        enable_dpi_awareness()
        last_result = None
        last_fingerprint = None
        last_mode = None
        last_ocr = 0.0
        unchanged = 0

        while not SHUTDOWN.is_set():
            cfg = dict(CFG)
            base = max(0.20, float(cfg.get("interval", 0.5)))
            idle_max = max(base, float(cfg.get("idle_interval", 3.0)))
            ocr_refresh = max(1.0, float(cfg.get("ocr_refresh", 5.0)))

            with STATE_LOCK:
                running = STATE["running"]

            if not running:
                last_fingerprint = None
                self.wake.wait(0.5)
                self.wake.clear()
                continue

            started = time.monotonic()
            try:
                if not IS_WINDOWS:
                    self.wake.wait(1.0)
                    self.wake.clear()
                    continue

                win = find_game_window(cfg)
                if not win:
                    last_fingerprint = None
                    self.wake.wait(idle_max)
                    self.wake.clear()
                    continue

                client = win["client"]
                char_img = grab_region(client, CHAR_TITLE)
                game_img = grab_region(client, GAME_TITLE)
                mode = classify_screen(char_img, game_img)

                if mode == "unknown":
                    last_mode = "unknown"
                    unchanged += 1
                else:
                    title_img = char_img if mode == "character" else game_img
                    fp = title_fingerprint(title_img)
                    now = time.monotonic()

                    if (fp != last_fingerprint or mode != last_mode
                            or (now - last_ocr) >= ocr_refresh):
                        parsed, raw = ocr_title(title_img, mode, cfg)
                        parsed["mode"] = mode
                        last_fingerprint = fp
                        last_mode = mode
                        last_ocr = now

                        if (parsed["level"] is not None
                                and parsed["school"] is not None):
                            changed = (
                                last_result is None
                                or parsed["level"] != last_result["level"]
                                or parsed["school"] != last_result["school"]
                            )
                            last_result = parsed
                            publish_result(parsed)
                            if changed:
                                unchanged = 0
                                log(f"read: Level {parsed['level']} {parsed['rank']} "
                                    f"{element_name(parsed['school'])} ({mode} screen)")
                            else:
                                unchanged += 1
                        else:
                            unchanged += 1
                    else:
                        unchanged += 1

            except Exception as exc:
                log(f"reader error: {exc}", level="warn")
                self.wake.wait(2.0)
                self.wake.clear()
                continue

            if unchanged >= 8:
                poll = min(idle_max, base * (1.6 ** min(6, unchanged - 7)))
            else:
                poll = base

            elapsed = time.monotonic() - started
            self.wake.wait(max(0.05, poll - elapsed))
            self.wake.clear()


class Controller:
    def __init__(self):
        self.reader = Reader()
        self.reader.start()
        self.watch = LevelWatch()
        self.watch.start()

    def learn_sound_async(self, seconds=2.2):
        def worker():
            ok, message = AUDIO.learn(seconds)
            log(f"learn sound: {message}", level="info" if ok else "warn")
        threading.Thread(target=worker, name="WizStreamBotLearn", daemon=True).start()

    def start(self):
        with STATE_LOCK:
            already = STATE["running"]
            STATE["running"] = True
        self.reader.wake.set()
        self.watch.wake.set()
        if not already:
            log("reader started")
        return True

    def stop(self):
        with STATE_LOCK:
            already = STATE["running"]
            STATE["running"] = False
        self.reader.wake.set()
        if already:
            log("reader stopped")
        return True

    def is_running(self):
        with STATE_LOCK:
            return STATE["running"]

    def read_once_async(self):
        def worker():
            try:
                result = read_once(dict(CFG))
                if result:
                    if result.get("level") and result.get("school"):
                        publish_result(result)
                        log(f"test read: Level {result['level']} {result['rank']} "
                            f"{element_name(result['school'])} ({result['mode']} screen)")
                    else:
                        log("test read: title unreadable", level="warn")
                else:
                    log("test read: Wizard101 not found", level="warn")
            except Exception as exc:
                log(f"test read failed: {exc}", level="warn")

        threading.Thread(target=worker, name="WizStreamBotTest", daemon=True).start()


# ============================================================================
# WEB SERVER
# ============================================================================

CONTROLLER = None


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        path = urlparse(self.path).path
        query = parse_qs(urlparse(self.path).query)

        if path == "/":
            self.send_dashboard()
        elif path == "/overlay" or path == "/obs":
            self.send_overlay()
        elif path == "/api/status":
            self.send_json(get_state())
        elif path == "/api/config":
            self.send_json(get_config())
        elif path == "/api/log":
            self.send_json({"entries": get_logs()})
        else:
            self.send_404()

    def do_POST(self):
        path = urlparse(self.path).path
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length).decode("utf-8", errors="replace")

        if path == "/api/control":
            data = json.loads(body) if body else {}
            action = data.get("action", "").strip()
            if action == "start":
                CONTROLLER.start()
                self.send_json({"status": "ok", "running": CONTROLLER.is_running()})
            elif action == "stop":
                CONTROLLER.stop()
                self.send_json({"status": "ok", "running": CONTROLLER.is_running()})
            elif action == "toggle":
                if CONTROLLER.is_running():
                    CONTROLLER.stop()
                else:
                    CONTROLLER.start()
                self.send_json({"status": "ok", "running": CONTROLLER.is_running()})
            elif action == "read_once":
                CONTROLLER.read_once_async()
                self.send_json({"status": "ok"})
            elif action == "bump_level":
                try:
                    delta = int(data.get("delta", 1))
                except (TypeError, ValueError):
                    delta = 1
                counted = register_levelup("manual", delta=delta, force=True)
                self.send_json({"status": "ok", "counted": counted, "state": get_state()})
            elif action == "learn_sound":
                try:
                    seconds = float(data.get("seconds", 2.2))
                except (TypeError, ValueError):
                    seconds = 2.2
                CONTROLLER.learn_sound_async(max(0.8, min(5.0, seconds)))
                self.send_json({"status": "ok"})
            elif action == "audio_status":
                self.send_json({"status": "ok", "text": AUDIO.status(),
                                "error": AUDIO.error})
            elif action == "shutdown":
                log("shutdown requested")
                SHUTDOWN.set()
                self.send_json({"status": "shutting down"})
            else:
                self.send_json({"error": "unknown action"}, 400)
        elif path == "/api/config":
            try:
                data = json.loads(body) if body else {}
                updated = set_config(data)
                _TESS_CACHE["checked"] = False
                _TESS_CACHE["path"] = None
                log("settings updated")
                self.send_json({"status": "saved", "config": updated})
            except Exception as exc:
                self.send_json({"error": str(exc)}, 400)
        else:
            self.send_404()

    def send_dashboard(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.wfile.write(DASHBOARD_HTML.encode("utf-8"))

    def send_overlay(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.wfile.write(OVERLAY_HTML.encode("utf-8"))

    def send_json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode("utf-8"))

    def send_404(self):
        self.send_response(404)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()
        self.wfile.write(b"Not found")

    def log_message(self, format, *args):
        pass  # suppress request logging


def find_free_port(start_port):
    for port in range(start_port, start_port + 10):
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.bind(("127.0.0.1", port))
            s.close()
            return port
        except OSError:
            pass
    return None


# ============================================================================
# HTML PAGES
# ============================================================================

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>WizStreamBot - Dashboard</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            background: #1a1a2e;
            color: #e0e0e0;
            line-height: 1.6;
        }
        .container { max-width: 1000px; margin: 0 auto; padding: 20px; }
        h1 { color: #fff; margin-bottom: 10px; font-size: 32px; }
        .version { color: #888; font-size: 12px; }
        
        .card {
            background: #16213e;
            border: 1px solid #444;
            border-radius: 8px;
            padding: 20px;
            margin: 15px 0;
        }
        
        .status-box {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 15px;
            margin: 15px 0;
        }
        
        .status-item {
            background: #0f3460;
            padding: 15px;
            border-radius: 6px;
            border-left: 4px solid #e94560;
        }
        
        .status-label { font-size: 12px; color: #aaa; text-transform: uppercase; }
        .status-value { font-size: 24px; font-weight: bold; color: #fff; margin-top: 5px; }
        .status-value.empty { color: #666; font-size: 16px; }
        
        .button-group {
            display: flex;
            gap: 10px;
            margin: 15px 0;
            flex-wrap: wrap;
        }
        
        button {
            padding: 10px 20px;
            border: none;
            border-radius: 6px;
            font-size: 14px;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.2s;
        }
        
        .btn-primary {
            background: #e94560;
            color: white;
        }
        .btn-primary:hover { background: #d63552; }
        .btn-primary.active { background: #27ae60; }
        
        .btn-secondary {
            background: #0f3460;
            color: #e0e0e0;
            border: 1px solid #e94560;
        }
        .btn-secondary:hover { background: #1a4d7a; }
        
        .btn-small {
            padding: 8px 16px;
            font-size: 12px;
        }
        
        .log-container {
            background: #0a0e27;
            border: 1px solid #333;
            border-radius: 6px;
            padding: 15px;
            height: 300px;
            overflow-y: auto;
            font-family: "Monaco", "Courier New", monospace;
            font-size: 12px;
        }
        
        .log-entry {
            padding: 4px 0;
            border-bottom: 1px solid #222;
        }
        
        .log-time { color: #666; }
        .log-text { color: #0f0; }
        .log-warn { color: #ff9800; }
        .log-error { color: #e94560; }
        
        .settings-form {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 15px;
            margin: 15px 0;
        }
        
        .form-group {
            display: flex;
            flex-direction: column;
        }
        
        .form-group label {
            font-size: 12px;
            color: #aaa;
            text-transform: uppercase;
            margin-bottom: 5px;
        }
        
        .form-group input,
        .form-group select {
            padding: 8px;
            background: #0f3460;
            border: 1px solid #333;
            color: #e0e0e0;
            border-radius: 4px;
            font-size: 14px;
        }
        
        .form-group input:focus,
        .form-group select:focus {
            outline: none;
            border-color: #e94560;
            background: #1a4d7a;
        }
        
        .info { color: #888; font-size: 12px; margin-top: 20px; }
        .overlay-link { color: #e94560; text-decoration: none; font-weight: 600; }
        .overlay-link:hover { text-decoration: underline; }
    </style>
</head>
<body>
    <div class="container">
        <h1>WizStreamBot <span class="version">v3.0.0</span></h1>
        
        <div class="card">
            <h2 style="margin-bottom: 15px;">Live Status</h2>
            <div class="status-box">
                <div class="status-item">
                    <div class="status-label">Level</div>
                    <div class="status-value" id="display-level"><span class="empty">--</span></div>
                </div>
                <div class="status-item" style="border-left-color: #ffd447;">
                    <div class="status-label">School</div>
                    <div class="status-value" id="display-school"><span class="empty">--</span></div>
                </div>
                <div class="status-item" style="border-left-color: #27ae60;">
                    <div class="status-label">Rank</div>
                    <div class="status-value" id="display-rank"><span class="empty">--</span></div>
                </div>
                <div class="status-item" style="border-left-color: #5fd0ff;">
                    <div class="status-label">Status</div>
                    <div class="status-value" id="display-running"><span class="empty">Stopped</span></div>
                </div>
            </div>
        </div>
        
        <div class="card">
            <h2 style="margin-bottom: 15px;">Control</h2>
            <div class="button-group">
                <button class="btn-primary" onclick="startReader()">START Reader</button>
                <button class="btn-primary" onclick="stopReader()">STOP Reader</button>
                <button class="btn-secondary btn-small" onclick="readOnce()">Read Once Now</button>
                <button class="btn-secondary btn-small" onclick="clearLogs()">Clear Log</button>
            </div>
        </div>
        
        <div class="card">
            <h2 style="margin-bottom: 15px;">Level Up Detection</h2>
            <p style="color:#aaa; font-size:13px; margin-bottom:12px;">
                Adds a level the moment the LEVEL UP banner appears, so you don't have to
                open the character sheet. The next real sheet read overrides it, so a
                miscount never sticks.
            </p>
            <div class="status-box">
                <div class="status-item" style="border-left-color:#c46bd4;">
                    <div class="status-label">Levels counted since last sheet read</div>
                    <div class="status-value" id="display-bumps">0</div>
                </div>
                <div class="status-item" style="border-left-color:#c46bd4;">
                    <div class="status-label">Last trigger</div>
                    <div class="status-value" id="display-trigger"><span class="empty">none yet</span></div>
                </div>
                <div class="status-item" style="border-left-color:#888;">
                    <div class="status-label">Banner signal (gate opens above the set value)</div>
                    <div class="status-value" id="display-density">0.00000</div>
                </div>
                <div class="status-item" style="border-left-color:#888;">
                    <div class="status-label">Sound match</div>
                    <div class="status-value" id="display-audio"><span class="empty">off</span></div>
                </div>
            </div>
            <div class="button-group">
                <button class="btn-secondary btn-small" onclick="bumpLevel(1)">+1 Level</button>
                <button class="btn-secondary btn-small" onclick="bumpLevel(-1)">-1 Level</button>
                <button class="btn-secondary btn-small" onclick="learnSound()">Learn Level-Up Sound</button>
            </div>
            <p style="color:#888; font-size:12px;">
                To teach it the sound: tick <em>Listen for the level-up sound</em>, save settings,
                then level up and press <em>Learn Level-Up Sound</em> within about three seconds.
                Needs <code>pip install sounddevice numpy</code>.
            </p>
        </div>

        <div class="card">
            <h2 style="margin-bottom: 15px;">Settings</h2>
            <div class="settings-form">
                <div class="form-group">
                    <label>Check Interval (s)</label>
                    <input type="number" id="cfg-interval" min="0.2" max="5" step="0.1">
                </div>
                <div class="form-group">
                    <label>Idle Interval (s)</label>
                    <input type="number" id="cfg-idle_interval" min="0.5" max="30" step="0.5">
                </div>
                <div class="form-group">
                    <label>OCR Refresh (s)</label>
                    <input type="number" id="cfg-ocr_refresh" min="1" max="120" step="1">
                </div>
                <div class="form-group">
                    <label>OCR Upscale</label>
                    <input type="number" id="cfg-ocr_upscale" min="2" max="5" step="1">
                </div>
                <div class="form-group">
                    <label>Min Level</label>
                    <input type="number" id="cfg-min_level" min="1" max="200" step="1">
                </div>
                <div class="form-group">
                    <label>Max Level</label>
                    <input type="number" id="cfg-max_level" min="1" max="200" step="1">
                </div>
                <div class="form-group">
                    <label>Tesseract Path</label>
                    <input type="text" id="cfg-tesseract_path" placeholder="Auto-detect">
                </div>
                <div class="form-group">
                    <label>Trigger Process</label>
                    <input type="text" id="cfg-trigger_process" placeholder="WizardGraphicalClient.exe">
                </div>
                <div class="form-group">
                    <label>Window Title Hint</label>
                    <input type="text" id="cfg-window_title_hint" placeholder="Wizard101">
                </div>
                <div class="form-group">
                    <label>Debug Mode</label>
                    <input type="checkbox" id="cfg-debug" style="width: 20px; height: 20px;">
                </div>
                <div class="form-group">
                    <label>Watch screen for LEVEL UP</label>
                    <input type="checkbox" id="cfg-levelup_visual" style="width: 20px; height: 20px;">
                </div>
                <div class="form-group">
                    <label>Listen for the level-up sound</label>
                    <input type="checkbox" id="cfg-levelup_audio" style="width: 20px; height: 20px;">
                </div>
                <div class="form-group">
                    <label>Scan Area (x,y,w,h as 0-1)</label>
                    <input type="text" id="cfg-levelup_band" placeholder="0.12,0.16,0.76,0.48">
                </div>
                <div class="form-group">
                    <label>Banner Gate (raise if it false-fires)</label>
                    <input type="number" id="cfg-levelup_gate" min="0.0002" max="0.05" step="0.0002">
                </div>
                <div class="form-group">
                    <label>Cooldown Between Levels (s)</label>
                    <input type="number" id="cfg-levelup_cooldown" min="2" max="120" step="1">
                </div>
                <div class="form-group">
                    <label>Check Interval (s)</label>
                    <input type="number" id="cfg-levelup_tick" min="0.1" max="2" step="0.05">
                </div>
                <div class="form-group">
                    <label>Sound Match Threshold</label>
                    <input type="number" id="cfg-levelup_audio_threshold" min="0.5" max="0.99" step="0.01">
                </div>
                <div class="form-group">
                    <label>Text File Folder (for OBS text sources)</label>
                    <input type="text" id="cfg-text_out_dir" placeholder="C:\\Users\\you\\Documents\\OBS FILES">
                </div>
            </div>
            <div class="button-group">
                <button class="btn-primary" onclick="saveConfig()">Save Settings</button>
                <button class="btn-secondary btn-small" onclick="loadConfig()">Reload</button>
            </div>
        </div>
        
        <div class="card">
            <h2 style="margin-bottom: 15px;">Log</h2>
            <div class="log-container" id="log-container"></div>
        </div>
        
        <div class="info">
            <strong>OBS Setup:</strong> Add a Browser source pointing to
            <a class="overlay-link" href="/overlay" target="_blank">http://127.0.0.1:8765/overlay</a>
            (no background, transparent, displays school + level)
        </div>
    </div>

    <script>
        const API_BASE = "";
        let pollInterval = null;

        function updateStatus() {
            fetch(API_BASE + "/api/status")
                .then(r => r.json())
                .then(data => {
                    document.getElementById("display-level").textContent = data.level || "--";
                    document.getElementById("display-school").textContent = data.school || "--";
                    document.getElementById("display-rank").textContent = data.rank || "--";
                    document.getElementById("display-running").textContent =
                        data.running ? "Running" : "Stopped";
                    document.getElementById("display-running").parentElement.parentElement.style.borderLeftColor =
                        data.running ? "#27ae60" : "#e94560";

                    const bumps = data.bumps || 0;
                    document.getElementById("display-bumps").textContent =
                        bumps + (data.base_level ? " (sheet said " + data.base_level + ")" : "");
                    const trig = document.getElementById("display-trigger");
                    if (data.levelup_at) {
                        const ago = Math.max(0, Math.round(Date.now() / 1000 - data.levelup_at));
                        trig.textContent = data.levelup_source + " - " +
                            (ago < 60 ? ago + "s ago" : Math.round(ago / 60) + "m ago");
                    } else {
                        trig.innerHTML = "<span class='empty'>none yet</span>";
                    }
                    document.getElementById("display-density").textContent =
                        (data.levelup_density || 0).toFixed(5);
                    const audio = document.getElementById("display-audio");
                    if (data.audio_state === "listening") {
                        audio.textContent = (data.audio_score || 0).toFixed(3);
                    } else {
                        audio.innerHTML = "<span class='empty'>" + (data.audio_state || "off") + "</span>";
                    }
                })
                .catch(e => console.error("status fetch:", e));
        }

        function bumpLevel(delta) {
            fetch(API_BASE + "/api/control", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify({action: "bump_level", delta: delta})
            }).then(() => updateStatus()).catch(e => console.error(e));
        }

        function learnSound() {
            fetch(API_BASE + "/api/control", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify({action: "learn_sound", seconds: 2.2})
            }).then(() => setTimeout(updateLog, 400)).catch(e => console.error(e));
        }

        function updateLog() {
            fetch(API_BASE + "/api/log")
                .then(r => r.json())
                .then(data => {
                    const container = document.getElementById("log-container");
                    const entries = data.entries || [];
                    if (entries.length > 0) {
                        container.innerHTML = entries.map(e =>
                            `<div class="log-entry"><span class="log-time">${e.time}</span> ` +
                            `<span class="log-${e.level}">${e.text}</span></div>`
                        ).join("");
                        container.scrollTop = container.scrollHeight;
                    }
                })
                .catch(e => console.error("log fetch:", e));
        }

        function startReader() {
            fetch(API_BASE + "/api/control", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify({action: "start"})
            }).then(() => updateStatus()).catch(e => console.error(e));
        }

        function stopReader() {
            fetch(API_BASE + "/api/control", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify({action: "stop"})
            }).then(() => updateStatus()).catch(e => console.error(e));
        }

        function readOnce() {
            fetch(API_BASE + "/api/control", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify({action: "read_once"})
            }).then(() => {
                setTimeout(updateStatus, 500);
                setTimeout(updateLog, 500);
            }).catch(e => console.error(e));
        }

        function clearLogs() {
            if (confirm("Clear the log?")) {
                document.getElementById("log-container").innerHTML = "";
            }
        }

        function loadConfig() {
            fetch(API_BASE + "/api/config")
                .then(r => r.json())
                .then(data => {
                    Object.keys(data).forEach(key => {
                        const el = document.getElementById("cfg-" + key);
                        if (el) {
                            if (el.type === "checkbox") {
                                el.checked = data[key];
                            } else {
                                el.value = data[key];
                            }
                        }
                    });
                })
                .catch(e => console.error(e));
        }

        function saveConfig() {
            const data = {};
            document.querySelectorAll("[id^='cfg-']").forEach(el => {
                const key = el.id.substring(4);
                data[key] = el.type === "checkbox" ? el.checked : el.value;
            });
            fetch(API_BASE + "/api/config", {
                method: "POST",
                headers: {"Content-Type": "application/json"},
                body: JSON.stringify(data)
            }).then(() => {
                alert("Settings saved");
                loadConfig();
            }).catch(e => console.error(e));
        }

        window.addEventListener("load", () => {
            loadConfig();
            updateStatus();
            updateLog();
            pollInterval = setInterval(() => {
                updateStatus();
                updateLog();
            }, 500);
        });

        window.addEventListener("beforeunload", () => {
            if (pollInterval) clearInterval(pollInterval);
        });
    </script>
</body>
</html>"""

OVERLAY_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>WizStreamBot Overlay</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        html, body { width: 100%; height: 100%; }
        body {
            background: transparent;
            display: flex;
            align-items: center;
            justify-content: center;
            font-family: "Arial", sans-serif;
        }
        
        .overlay-container {
            display: flex;
            flex-direction: column;
            align-items: center;
            justify-content: center;
            background: transparent;
            text-align: center;
        }
        
        .school-name {
            font-size: 48px;
            font-weight: bold;
            color: #ffd447;
            text-shadow: 2px 2px 4px rgba(0, 0, 0, 0.8);
            margin-bottom: 10px;
            letter-spacing: 2px;
        }
        
        .level-display {
            font-size: 64px;
            font-weight: bold;
            color: #ffffff;
            text-shadow: 2px 2px 6px rgba(0, 0, 0, 0.9),
                        0 0 10px rgba(255, 212, 71, 0.5);
            line-height: 1;
        }
        
        .levelup-flash {
            margin-top: 6px;
            font-size: 26px;
            font-weight: 800;
            letter-spacing: 0.18em;
            color: #ffd447;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.9), 0 0 14px rgba(255,212,71,0.6);
            animation: pulse 0.9s ease-in-out infinite;
        }
        @keyframes pulse {
            0%, 100% { opacity: 0.65; }
            50%      { opacity: 1; }
        }

        .status-offline {
            font-size: 32px;
            color: #999;
            text-shadow: 1px 1px 3px rgba(0, 0, 0, 0.8);
        }
    </style>
</head>
<body>
    <div class="overlay-container" id="overlay">
        <div class="status-offline">Waiting...</div>
    </div>

    <script>
        const schoolColors = {
            "Fire": "#ff6a2a",
            "Ice": "#5fd0ff",
            "Storm": "#a86bff",
            "Life": "#57d98a",
            "Death": "#9d8fb5",
            "Myth": "#ffd447",
            "Balance": "#e6c07a"
        };

        let lastLevel = null;
        let flashUntil = 0;

        function updateOverlay() {
            fetch("/api/status")
                .then(r => r.json())
                .then(data => {
                    const container = document.getElementById("overlay");
                    if (data.level && data.school) {
                        if (lastLevel !== null && data.level > lastLevel) {
                            flashUntil = Date.now() + 5000;
                        }
                        lastLevel = data.level;
                        const color = schoolColors[data.school] || "#ffd447";
                        const flashing = Date.now() < flashUntil;
                        container.innerHTML = `
                            <div class="school-name" style="color: ${color};">${data.school}</div>
                            <div class="level-display"${flashing ? ' style="color:#ffe8b0;"' : ''}>Level ${data.level}</div>
                            ${flashing ? '<div class="levelup-flash">LEVEL UP!</div>' : ''}
                        `;
                    } else {
                        container.innerHTML = `<div class="status-offline">Waiting...</div>`;
                    }
                })
                .catch(e => {
                    console.error("fetch failed:", e);
                    document.getElementById("overlay").innerHTML = `<div class="status-offline">Error</div>`;
                });
        }

        window.addEventListener("load", () => {
            updateOverlay();
            setInterval(updateOverlay, 700);
        });
    </script>
</body>
</html>"""


# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="WizStreamBot - Wizard101 reader")
    parser.add_argument("--port", type=int, default=DEFAULT_PORT,
                       help=f"Port (default {DEFAULT_PORT})")
    parser.add_argument("--no-browser", action="store_true",
                       help="Don't open browser on start")
    parser.add_argument("--host", default="127.0.0.1", help="Host (default 127.0.0.1)")
    parser.add_argument("command", nargs="?", default="serve",
                       help="serve (default), test, band, listen")
    args = parser.parse_args()

    if args.command == "band":
        enable_dpi_awareness()
        if not IS_WINDOWS:
            print("Window capture is Windows-only")
            return
        win = find_game_window(CFG)
        if not win:
            print("Wizard101 window not found")
            return
        img = grab_region(win["client"], parse_band(CFG.get("levelup_band")))
        out = Path(__file__).resolve().with_name("levelup_band.png")
        img.save(out)
        print(f"Saved {out}")
        print(f"Magenta density right now: {levelup_density(img):.5f}")
        print("Open that PNG - the LEVEL UP banner must sit fully inside it.")
        return

    if args.command == "listen":
        enable_dpi_awareness()
        if not IS_WINDOWS:
            print("Window capture is Windows-only")
            return
        print("Watching the scan area. Go level up - Ctrl+C to stop.\n")
        peak = 0.0
        try:
            while True:
                win = find_game_window(CFG)
                if not win:
                    print("  waiting for Wizard101...", end="\r")
                    time.sleep(1.0)
                    continue
                img = grab_region(win["client"], parse_band(CFG.get("levelup_band")))
                density = levelup_density(img)
                peak = max(peak, density)
                flag = ""
                if density >= float(CFG.get("levelup_gate", 0.0012)):
                    hit, raw = confirm_levelup(img, CFG)
                    flag = f"  GATE OPEN -> {'MATCH' if hit else 'no match'}  [{raw[:40]}]"
                print(f"  density {density:.5f}   peak {peak:.5f}{flag}          ", end="\r")
                if flag:
                    print()
                time.sleep(0.25)
        except KeyboardInterrupt:
            print(f"\n\nPeak density seen: {peak:.5f}")
            print("Set the gate to roughly a third of the peak you saw while the banner was up.")
        return

    if args.command == "test":
        enable_dpi_awareness()
        try:
            from PIL import Image
            print("✓ Pillow installed")
        except ImportError:
            print("✗ Pillow missing - pip install pillow")
            return
        exe = find_tesseract(CFG)
        print(f"✓ Tesseract: {exe or 'NOT FOUND'}")
        if not IS_WINDOWS:
            print("(Window capture is Windows-only)")
            return
        win = find_game_window(CFG)
        if not win:
            print("✗ Wizard101 window not found")
            return
        print(f"✓ Wizard101: {win['title']} ({win['client'][2]}x{win['client'][3]})")
        result = read_once(CFG)
        if not result:
            print("✗ No title found on screen")
        elif result.get("level") and result.get("school"):
            print(f"✓ Read: Level {result['level']} {result['rank']} "
                  f"{element_name(result['school'])} ({result['mode']} screen)")
        else:
            print(f"✗ Title found but unreadable: {result.get('raw', '')}")
        return

    global CONTROLLER
    CONTROLLER = Controller()
    log(f"WizStreamBot {APP_VERSION} started")

    port = find_free_port(args.port)
    if not port:
        print(f"ERROR: No free port starting from {args.port}")
        sys.exit(1)

    server = ThreadingHTTPServer((args.host, port), Handler)
    url = f"http://{args.host}:{port}/"
    log(f"listening on {url}")

    if not args.no_browser:
        try:
            webbrowser.open(url)
        except Exception as exc:
            log(f"could not open browser: {exc}", level="warn")

    try:
        while not SHUTDOWN.is_set():
            server.handle_request()
    except KeyboardInterrupt:
        log("interrupted")
    finally:
        SHUTDOWN.set()
        server.server_close()
        log("shutdown complete")


if __name__ == "__main__":
    main()
