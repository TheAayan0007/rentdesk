#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RentDesk - a modern rent & renter manager
=========================================

Run it
    pip install PyQt6
    python rent_manager.py

Where is my data?
    Everything lives in a folder called "rent_data" next to this file:
        rent_data/rentdesk.db          the SQLite database
        rent_data/profile_photos/      uploaded profile pictures
        rent_data/aadhaar_cards/       uploaded Aadhaar card images (front & back)
        rent_data/.cache/              thumbnails and temporary pages rendered from PDFs
    Copy that folder to move or back up your data.

Optional: auto-fill from an Aadhaar photo/PDF
    RentDesk can try to read the Aadhaar number, name, DOB, gender, father's/
    guardian's name and address straight off an uploaded card and fill the
    form for you. This needs two extra, optional packages plus the Tesseract
    OCR engine itself:
        pip install pytesseract Pillow PyMuPDF
        # then install the Tesseract binary:
        #   Windows : https://github.com/UB-Mannheim/tesseract/wiki
        #   macOS   : brew install tesseract
        #   Linux   : sudo apt install tesseract-ocr
    None of this is required - if it isn't installed, the Aadhaar fields are
    simply left blank for you to fill in by hand.
"""
from __future__ import annotations

import os
import re
import sys
import math
import random
import shutil
import sqlite3
import zipfile
import traceback
import subprocess
import urllib.parse
import webbrowser
from datetime import datetime, date
from pathlib import Path

# -- optional Aadhaar OCR helpers -------------------------------------------------
# All of these are optional. If they aren't installed, auto-fill is silently
# skipped and the person can still type the Aadhaar details in by hand.
try:
    import pytesseract
    from PIL import Image as PILImage
except ImportError:
    pytesseract = None
    PILImage = None

try:
    import fitz  # PyMuPDF - used to turn a PDF's pages into images
except ImportError:
    fitz = None

OCR_AVAILABLE = pytesseract is not None and PILImage is not None
PDF_AVAILABLE = fitz is not None

try:
    from PyQt6.QtCore import (
        Qt, QObject, QEvent, QThread, QTimer, QSize, QPoint, QPointF, QRect, QRectF, QByteArray, QUrl,
        QEasingCurve, QPropertyAnimation, QParallelAnimationGroup, QSequentialAnimationGroup,
        QVariantAnimation, QAbstractAnimation, QRegularExpression, QDate, QStandardPaths,
        pyqtSignal, pyqtProperty,
    )
    from PyQt6.QtGui import (
        QColor, QPainter, QPainterPath, QPen, QBrush, QLinearGradient, QRadialGradient, QFont,
        QFontMetrics, QFontMetricsF, QPixmap, QImage, QImageReader, QIcon, QCursor, QGuiApplication,
        QKeySequence, QShortcut, QRegularExpressionValidator, QDesktopServices,
    )
    from PyQt6.QtWidgets import (
        QApplication, QWidget, QFrame, QLabel, QAbstractButton, QLineEdit, QPlainTextEdit,
        QDateEdit, QVBoxLayout, QHBoxLayout, QGridLayout, QScrollArea, QFileDialog,
        QGraphicsOpacityEffect, QGraphicsDropShadowEffect, QSizePolicy, QMenu, QToolTip,
    )
    from PyQt6.QtSvg import QSvgRenderer
except ImportError:  # pragma: no cover
    print("RentDesk needs PyQt6.  Install it with:\n\n    pip install PyQt6\n")
    sys.exit(1)

# ════════════════════════════════════════════════════════════════════════════
#  Paths & constants
# ════════════════════════════════════════════════════════════════════════════
APP_NAME = "RentDesk"
BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("RENTDESK_DATA") or (BASE_DIR / "rent_data"))
PHOTO_DIR = DATA_DIR / "profile_photos"
AADHAAR_DIR = DATA_DIR / "aadhaar_cards"
CACHE_DIR = DATA_DIR / ".cache"
DB_PATH = DATA_DIR / "rentdesk.db"
LOG_PATH = DATA_DIR / "error.log"

RELATIONS = ["Roommate", "Sibling", "Relative", "Friend", "Other"]
DUE_REASONS = ["Overdue rent", "Late fee", "Damage", "Electricity", "Other"]
GENDERS = ["Not specified", "Male", "Female", "Other"]
IMAGE_FILTER = "Images (*.png *.jpg *.jpeg *.webp *.bmp *.gif *.tif *.tiff)"
AADHAAR_FILTER = ("Aadhaar card - image or PDF (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff *.pdf)"
                   ";;Images (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff)"
                   ";;PDF (*.pdf)")

# ════════════════════════════════════════════════════════════════════════════
#  Theme - ink & paper, colour only where it means something
#     green  = send / paid / active      amber = dues      red = destructive
#     blue   = focus & selection         ink   = primary actions
# ════════════════════════════════════════════════════════════════════════════
PALETTES = {
    "light": dict(
        bg="#EDEFF3", surface="#FFFFFF", surface2="#F4F5F8", surface3="#E9ECF1",
        line="#E1E4EB", line2="#C9CFDB",
        text="#10131A", text2="#4A5160", text3="#727A8C",
        ink="#10131A", on_ink="#FFFFFF", ink_hi="#2A3040",
        blue="#3055F5", green="#14B86C", green_t="#0A7F46", green_hi="#0FA35F", on_green="#FFFFFF",
        amber="#E08A0B", amber_t="#B45309", red="#DC3B4F", red_t="#C42B40", slate="#6B7385",
        bubble="#DCF8C6", bubble_t="#0D2A17", shadow="#0B1020",
    ),
    "dark": dict(
        bg="#0E1116", surface="#161A21", surface2="#1C212A", surface3="#232936",
        line="#262C37", line2="#3A4353",
        text="#EEF1F6", text2="#A4ACBC", text3="#7C8599",
        ink="#F1F3F8", on_ink="#0E1116", ink_hi="#FFFFFF",
        blue="#7F97FF", green="#2FD07F", green_t="#4BDC93", green_hi="#3BE08C", on_green="#04150C",
        amber="#F6B04C", amber_t="#F6B04C", red="#FF6E82", red_t="#FF8496", slate="#8A93A6",
        bubble="#0F3D2C", bubble_t="#E4FBEF", shadow="#000000",
    ),
}


class Theme:
    mode = "light"

    @classmethod
    def hex(cls, name: str) -> str:
        return PALETTES[cls.mode][name]

    @classmethod
    def c(cls, name: str, alpha: float | None = None) -> QColor:
        col = QColor(PALETTES[cls.mode][name])
        if alpha is not None:
            col.setAlphaF(max(0.0, min(1.0, alpha)))
        return col

    @classmethod
    def dark(cls) -> bool:
        return cls.mode == "dark"


C = Theme.c


class Motion:
    """Global switch so every animation can be turned off from Settings."""
    on = True


def dur(ms: int) -> int:
    return int(ms) if Motion.on else 0


def mix(a: QColor, b: QColor, t: float) -> QColor:
    t = max(0.0, min(1.0, t))
    return QColor(
        round(a.red() + (b.red() - a.red()) * t),
        round(a.green() + (b.green() - a.green()) * t),
        round(a.blue() + (b.blue() - a.blue()) * t),
        round(a.alpha() + (b.alpha() - a.alpha()) * t),
    )


def rgba(hexcolor: str, alpha: float) -> str:
    c = QColor(hexcolor)
    return f"rgba({c.red()},{c.green()},{c.blue()},{alpha:.2f})"


# ── typography ──────────────────────────────────────────────────────────────
# Body text uses the system UI face. Numbers, names and headings use a DIN-style
# face (Bahnschrift ships with Windows 10/11) - it reads like a meter plate.
TEXT_FAMILIES = ["Segoe UI Variable Text", "Segoe UI", "SF Pro Text", "Helvetica Neue", "Inter",
                 "Noto Sans", "Liberation Sans", "DejaVu Sans", "Arial"]
DISPLAY_FAMILIES = ["Bahnschrift", "DIN Alternate", "Segoe UI Variable Display", "Segoe UI",
                    "SF Pro Display", "Helvetica Neue", "Inter", "Noto Sans", "Liberation Sans",
                    "DejaVu Sans", "Arial"]
W_NORMAL, W_MED, W_SEMI, W_BOLD = (QFont.Weight.Normal, QFont.Weight.Medium,
                                   QFont.Weight.DemiBold, QFont.Weight.Bold)


def font(px: float = 14, weight=QFont.Weight.Normal, display: bool = False) -> QFont:
    f = QFont()
    f.setFamilies(DISPLAY_FAMILIES if display else TEXT_FAMILIES)
    f.setPixelSize(round(px))
    f.setWeight(weight)
    f.setStyleStrategy(QFont.StyleStrategy.PreferAntialias)
    return f


# ════════════════════════════════════════════════════════════════════════════
#  Icons (24x24 stroke icons, rendered from inline SVG so they follow the theme)
# ════════════════════════════════════════════════════════════════════════════
ICONS = {
    "plus": '<path d="M12 5v14M5 12h14"/>',
    "arrow-right": '<path d="M5 12h14M12 5l7 7-7 7"/>',
    "arrow-left": '<path d="M19 12H5M12 19l-7-7 7-7"/>',
    "x": '<path d="M18 6L6 18M6 6l12 12"/>',
    "check": '<path d="M20 6L9 17l-5-5"/>',
    "chevron-right": '<path d="M9 18l6-6-6-6"/>',
    "chevron-left": '<path d="M15 18l-6-6 6-6"/>',
    "chevron-down": '<path d="M6 9l6 6 6-6"/>',
    "user": '<path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/>',
    "users": '<path d="M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M23 21v-2a4 4 0 0 0-3-3.87M16 3.13a4 4 0 0 1 0 7.75"/>',
    "phone": '<path d="M22 16.92v3a2 2 0 0 1-2.18 2 19.79 19.79 0 0 1-8.63-3.07 19.5 19.5 0 0 1-6-6 19.79 19.79 0 0 1-3.07-8.67A2 2 0 0 1 4.11 2h3a2 2 0 0 1 2 1.72 12.84 12.84 0 0 0 .7 2.81 2 2 0 0 1-.45 2.11L8.09 9.91a16 16 0 0 0 6 6l1.27-1.27a2 2 0 0 1 2.11-.45 12.84 12.84 0 0 0 2.81.7A2 2 0 0 1 22 16.92z"/>',
    "home": '<path d="M3 9l9-7 9 7v11a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/><path d="M9 22V12h6v10"/>',
    "key": '<path d="M21 2l-2 2m-7.61 7.61a5.5 5.5 0 1 1-7.778 7.778 5.5 5.5 0 0 1 7.777-7.777zm0 0L15.5 7.5m0 0l3 3L22 7l-3-3m-3.5 3.5L19 4"/>',
    "trash": '<path d="M3 6h18M19 6l-1 14a2 2 0 0 1-2 2H8a2 2 0 0 1-2-2L5 6M10 11v6M14 11v6M9 6V4a1 1 0 0 1 1-1h4a1 1 0 0 1 1 1v2"/>',
    "edit": '<path d="M12 20h9"/><path d="M16.5 3.5a2.121 2.121 0 0 1 3 3L7 19l-4 1 1-4L16.5 3.5z"/>',
    "download": '<path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4M7 10l5 5 5-5M12 15V3"/>',
    "upload": '<path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4M17 8l-5-5-5 5M12 3v12"/>',
    "image": '<rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><path d="M21 15l-5-5L5 21"/>',
    "camera": '<path d="M23 19a2 2 0 0 1-2 2H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h4l2-3h6l2 3h4a2 2 0 0 1 2 2z"/><circle cx="12" cy="13" r="4"/>',
    "id-card": '<rect x="2" y="5" width="20" height="14" rx="2"/><circle cx="8" cy="11" r="2"/><path d="M14 9h4M14 13h4M5.5 16c.6-1.2 1.6-2 2.5-2s1.9.8 2.5 2"/>',
    "link": '<path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"/><path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/>',
    "search": '<circle cx="11" cy="11" r="8"/><path d="M21 21l-4.35-4.35"/>',
    "sun": '<circle cx="12" cy="12" r="5"/><path d="M12 1v2M12 21v2M4.22 4.22l1.42 1.42M18.36 18.36l1.42 1.42M1 12h2M21 12h2M4.22 19.78l1.42-1.42M18.36 5.64l1.42-1.42"/>',
    "moon": '<path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/>',
    "sliders": '<path d="M4 21v-7M4 10V3M12 21v-9M12 8V3M20 21v-5M20 12V3M1 14h6M9 8h6M17 16h6"/>',
    "copy": '<rect x="9" y="9" width="13" height="13" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/>',
    "send": '<path d="M22 2L11 13M22 2l-7 20-4-9-9-4 20-7z"/>',
    "zap": '<path d="M13 2L3 14h9l-1 8 10-12h-9l1-8z"/>',
    "wifi": '<path d="M5 12.55a11 11 0 0 1 14.08 0M1.42 9a16 16 0 0 1 21.16 0M8.53 16.11a6 6 0 0 1 6.95 0M12 20h.01"/>',
    "file-text": '<path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/><path d="M14 2v6h6M16 13H8M16 17H8M10 9H8"/>',
    "more": '<circle cx="12" cy="12" r="1"/><circle cx="19" cy="12" r="1"/><circle cx="5" cy="12" r="1"/>',
    "calendar": '<rect x="3" y="4" width="18" height="18" rx="2"/><path d="M16 2v4M8 2v4M3 10h18"/>',
    "rupee": '<path d="M6 3h12M6 8h12M6 13l8.5 8M6 13h3M9 13c6.667 0 6.667-10 0-10"/>',
    "hash": '<path d="M4 9h16M4 15h16M10 3L8 21M16 3l-2 18"/>',
    "lock": '<rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/>',
    "alert": '<circle cx="12" cy="12" r="10"/><path d="M12 8v4M12 16h.01"/>',
    "log-out": '<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4M16 17l5-5-5-5M21 12H9"/>',
    "rotate": '<path d="M1 4v6h6"/><path d="M3.51 15a9 9 0 1 0 2.13-9.36L1 10"/>',
    "archive": '<path d="M21 8v13H3V8M1 3h22v5H1zM10 12h4"/>',
    "eye": '<path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/>',
    "check-circle": '<path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><path d="M22 4L12 14.01l-3-3"/>',
    "info": '<circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/>',
    "clock": '<circle cx="12" cy="12" r="10"/><path d="M12 6v6l4 2"/>',
    "message": '<path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/>',
    "folder": '<path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/>',
    "alert-triangle": '<path d="M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0zM12 9v4M12 17h.01"/>',
    "user-plus": '<path d="M16 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"/><circle cx="8.5" cy="7" r="4"/><path d="M20 8v6M23 11h-6"/>',
}

_svg_cache: dict = {}


def _qcolor(color) -> QColor:
    return color if isinstance(color, QColor) else QColor(color)


def icon_pm(name: str, color, size: int = 18, dpr: float = 2.0, stroke: float = 2.0) -> QPixmap:
    col = _qcolor(color)
    col = QColor(col.red() & ~7, col.green() & ~7, col.blue() & ~7, min(255, (col.alpha() + 8) // 16 * 16))
    key = (name, col.name(), col.alpha(), size, round(dpr, 2), stroke)
    pm = _svg_cache.get(key)
    if pm is not None:
        return pm
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" '
           f'stroke="{col.name()}" stroke-opacity="{col.alphaF():.3f}" stroke-width="{stroke}" '
           f'stroke-linecap="round" stroke-linejoin="round">{ICONS[name]}</svg>')
    renderer = QSvgRenderer(QByteArray(svg.encode("utf-8")))
    px = max(1, int(round(size * dpr)))
    pm = QPixmap(px, px)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    renderer.render(p, QRectF(0, 0, px, px))
    p.end()
    pm.setDevicePixelRatio(dpr)
    _svg_cache[key] = pm
    return pm


def icon_file(name: str, color, size: int = 16) -> str:
    """Write an icon to a PNG in the cache folder (needed by Qt style sheets)."""
    col = _qcolor(color)
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    path = CACHE_DIR / f"ic_{name}_{col.name()[1:]}_{size}.png"
    if not path.exists():
        icon_pm(name, col, size, 2.0).save(str(path), "PNG")
    return path.as_posix()


class TWidget(QWidget):
    """QWidget that composites correctly against custom-painted ancestors.

    Qt/PyQt6 has a compositing quirk (verified on a real X server, not just the
    offscreen QPA): a plain QWidget nested inside a custom-painted ancestor
    (anything using QPainter to fill/round its own background in paintEvent)
    can render as a "hole" showing the top-level window's background instead
    of its actual parent's painted content, UNLESS the widget has been marked
    Qt::WA_StyledBackground and has at least one (even no-op) instance-level
    stylesheet. Every container/wrapper widget in this app - whether it paints
    its own animated background (Panel, FieldFrame, ...) or is a plain layout
    wrapper with no visual of its own - is built on TWidget/TFrame for this
    reason. This is unrelated to, and layered underneath, our light/dark theme
    stylesheet: the "background: transparent" below is a structural fix, not
    a visual one, and never overrides a subclass's own paintEvent.
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setStyleSheet("background: transparent;")


class TFrame(QFrame):
    """QFrame counterpart of TWidget - see TWidget's docstring."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setStyleSheet("background: transparent;")


def box(layout_cls=None, margins=(0, 0, 0, 0), spacing=0) -> QWidget:
    """A throwaway TWidget for grouping widgets in a layout - the safe replacement for a bare QWidget()."""
    w = TWidget()
    if layout_cls is not None:
        lay = layout_cls(w)
        lay.setContentsMargins(*margins)
        lay.setSpacing(spacing)
    return w


def screen_dpr() -> float:
    try:
        return max(1.0, QGuiApplication.primaryScreen().devicePixelRatio())
    except Exception:
        return 2.0


# ════════════════════════════════════════════════════════════════════════════
#  Global style sheet
# ════════════════════════════════════════════════════════════════════════════
# NOTE ON WHAT IS DELIBERATELY *NOT* HERE
# --------------------------------------------------------------------------
# This app nests plain Qt widgets (QLabel, QLineEdit, QPlainTextEdit, QDateEdit)
# inside custom-painted rounded containers (Panel, FieldFrame, ...) everywhere.
# A GLOBAL type-selector rule for any of those four types (even something as
# innocuous as "QLabel { color: ... }" with no background at all) makes Qt
# composite every instance of that type against the top-level window instead
# of its immediate parent - so a QLabel sitting on a white rounded card renders
# a hole showing the page background right through the card. This reproduces
# identically on a real X server (verified with Xvfb + the xcb platform, not
# just the offscreen QPA), so it is a genuine Qt/PyQt6 compositing quirk here,
# not a screenshot artifact. Scoping the same rule to each WIDGET INSTANCE
# (widget.setStyleSheet(...) on that one object) does not trigger it. So:
# QLabel is styled per-instance in _label_css()/label()/set_tone() (below),
# QLineEdit/QPlainTextEdit per-instance in Field.__init__, QDateEdit and its
# calendar popup per-instance in DateField.__init__ (_calendar_css()) - and
# none of the four appear as a bare type-selector in the stylesheet below.
# QMenu/QToolTip (true top-level popups) and QScrollBar (inside a plain,
# non-custom-painted QScrollArea) are not nested inside custom paint the same
# way, so they stay global.
QSS = """
QToolTip { background: @ink@; color: @on_ink@; border: none; padding: 6px 10px; border-radius: 8px; font-size: 12px; }
QScrollArea { background: transparent; border: none; }
QScrollBar:vertical { background: transparent; width: 14px; margin: 6px 2px 6px 2px; }
QScrollBar::handle:vertical { background: @line2@; border-radius: 4px; min-height: 40px; margin: 0 2px; }
QScrollBar::handle:vertical:hover { background: @text3@; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; background: none; }
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }
QScrollBar:horizontal { background: transparent; height: 14px; margin: 2px 6px 2px 6px; }
QScrollBar::handle:horizontal { background: @line2@; border-radius: 4px; min-width: 40px; margin: 2px 0; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; background: none; }
QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal { background: none; }
QMenu { background: @surface@; border: 1px solid @line@; border-radius: 14px; padding: 6px; }
QMenu::item { padding: 9px 18px 9px 14px; border-radius: 9px; color: @text@; font-size: 14px; margin: 1px 0; }
QMenu::item:selected { background: @surface3@; }
QMenu::separator { height: 1px; background: @line@; margin: 6px 8px; }
"""


def build_qss() -> str:
    p = PALETTES[Theme.mode]
    q = QSS
    for k, v in p.items():
        q = q.replace(f"@{k}@", v)
    return q


def _calendar_css() -> str:
    """Per-instance stylesheet for a QDateEdit's popup QCalendarWidget - see the note above."""
    p = PALETTES[Theme.mode]
    chev_l = icon_file("chevron-left", p["text2"], 16)
    chev_r = icon_file("chevron-right", p["text2"], 16)
    q = """
QCalendarWidget { background: @surface@; }
QCalendarWidget QWidget { background: @surface@; color: @text@; }
QCalendarWidget QToolButton { color: @text@; background: transparent; border: none; padding: 6px 10px;
    font-size: 14px; border-radius: 8px; icon-size: 16px; }
QCalendarWidget QToolButton:hover { background: @surface3@; }
QCalendarWidget QToolButton::menu-indicator { image: none; }
QCalendarWidget QMenu { background: @surface@; }
QCalendarWidget QSpinBox { background: @surface2@; color: @text@; border: none; border-radius: 6px; padding: 2px 6px;
    selection-background-color: @blue@; }
QCalendarWidget QAbstractItemView:enabled { color: @text@; background: @surface@; outline: 0;
    selection-background-color: @ink@; selection-color: @on_ink@; }
QCalendarWidget QAbstractItemView:disabled { color: @text3@; }
QCalendarWidget #qt_calendar_prevmonth { qproperty-icon: url(@ic_chev_left@); }
QCalendarWidget #qt_calendar_nextmonth { qproperty-icon: url(@ic_chev_right@); }
"""
    for k, v in {**p, "ic_chev_left": chev_l, "ic_chev_right": chev_r}.items():
        q = q.replace(f"@{k}@", v)
    return q


# ════════════════════════════════════════════════════════════════════════════
#  Formatting helpers
# ════════════════════════════════════════════════════════════════════════════
def now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def today_iso() -> str:
    return date.today().isoformat()


def parse_date(s: str | None):
    try:
        return date.fromisoformat((s or "")[:10])
    except Exception:
        return None


def pretty_date(s: str | None) -> str:
    d = parse_date(s)
    return d.strftime("%d %b %Y") if d else "-"


def pretty_dt(s: str | None) -> str:
    try:
        return datetime.fromisoformat(s).strftime("%d %b %Y, %I:%M %p")
    except Exception:
        return s or "-"


def to_float(text, default: float = 0.0) -> float:
    t = (text or "").strip().replace(",", "")
    return float(t) if t else default


def num(x) -> str:
    """12.0 -> '12', 12.5 -> '12.5', 12.345 -> '12.35'."""
    s = f"{float(x or 0):.2f}".rstrip("0").rstrip(".")
    return s if s not in ("", "-0") else "0"


def inr(x, plain: bool = False) -> str:
    """Indian digit grouping: 1234567 -> ₹12,34,567."""
    try:
        x = round(float(x or 0), 2)
    except (TypeError, ValueError):
        x = 0.0
    neg = x < 0
    whole, frac = f"{abs(x):.2f}".split(".")
    if len(whole) > 3:
        head, tail = whole[:-3], whole[-3:]
        head = re.sub(r"(\d)(?=(\d\d)+$)", r"\1,", head)
        whole = head + "," + tail
    out = whole + ("" if frac == "00" else "." + frac)
    return ("-" if neg else "") + ("" if plain else "₹") + out


def digits(s: str) -> str:
    return re.sub(r"\D", "", s or "")


def wa_number(phone: str, country_code: str = "91") -> str:
    """Phone number in the format WhatsApp links need (digits, with country code)."""
    d = digits(phone)
    if not d:
        return ""
    if d.startswith("00"):
        d = d[2:]
    elif len(d) == 11 and d.startswith("0"):
        d = country_code + d[1:]
    elif len(d) == 10:
        d = country_code + d
    return d


def safe_name(s: str) -> str:
    return re.sub(r"[^\w.-]+", "_", s or "", flags=re.UNICODE).strip("_") or "renter"


def initials(name: str) -> str:
    parts = [w for w in re.split(r"\s+", (name or "").strip()) if w]
    if not parts:
        return "?"
    if len(parts) == 1:
        return parts[0][:2].upper()
    return (parts[0][0] + parts[-1][0]).upper()


def days_overdue(iso: str) -> int | None:
    d = parse_date(iso)
    return (date.today() - d).days if d else None


# ════════════════════════════════════════════════════════════════════════════
#  Bill maths + WhatsApp message (same layout as the original tool)
# ════════════════════════════════════════════════════════════════════════════
def compute_bill(rent, primary, main, rate, wifi, back_dues, advance) -> dict:
    units = max(0.0, (main or 0) - (primary or 0))
    electricity = round(units * (rate or 0), 2)
    subtotal = round((rent or 0) + electricity + (wifi or 0) + (back_dues or 0) - (advance or 0), 2)
    return dict(units=units, electricity=electricity, subtotal=subtotal)


def build_message(name, phone, when: datetime, b: dict, note: str = "", include_note: bool = False) -> str:
    elec = f"Electricity Fee: {inr(b['electricity'])}"
    if b.get("has_reading"):
        elec += f"  ({num(b['units'])} units: {num(b['primary_unit'])} → {num(b['main_unit'])} @ {inr(b['unit_rate'])})"
    lines = [f"Name: {name}"]
    if phone:
        lines.append(f"Phone: {phone}")
    lines += [
        f"Date: {when:%d/%m/%Y}",
        f"Time: {when:%I:%M %p}",
        f"Total Rent: {inr(b['rent'])}",
        elec,
        f"WIFI Fee: {inr(b['wifi_fee'])}",
        f"Advance Paid: {inr(b['advance'])}",
        f"Back Dues: {inr(b['back_dues'])}",
        f"Subtotal==============> {inr(b['subtotal'])}",
    ]
    if include_note and (note or "").strip():
        lines.append(f"Note: {note.strip()}")
    return "\n".join(lines)


# ════════════════════════════════════════════════════════════════════════════
#  Database (SQLite)
# ════════════════════════════════════════════════════════════════════════════
SCHEMA = """
CREATE TABLE IF NOT EXISTS renters (
    id            INTEGER PRIMARY KEY CHECK (id BETWEEN 1000 AND 9999),
    name          TEXT    NOT NULL,
    phone         TEXT    NOT NULL DEFAULT '',
    alt_phone     TEXT    NOT NULL DEFAULT '',
    father_name   TEXT    NOT NULL DEFAULT '',
    mother_name   TEXT    NOT NULL DEFAULT '',
    parent_phone  TEXT    NOT NULL DEFAULT '',
    room_no       TEXT    NOT NULL DEFAULT '',
    monthly_rent  REAL    NOT NULL DEFAULT 0,
    wifi_fee      REAL    NOT NULL DEFAULT 0,
    unit_rate     REAL    NOT NULL DEFAULT 0,
    join_date     TEXT    NOT NULL DEFAULT '',
    notes         TEXT    NOT NULL DEFAULT '',
    photo_path    TEXT    NOT NULL DEFAULT '',
    aadhaar_path  TEXT    NOT NULL DEFAULT '',
    aadhaar_front_path TEXT NOT NULL DEFAULT '',
    aadhaar_back_path  TEXT NOT NULL DEFAULT '',
    aadhaar_number  TEXT  NOT NULL DEFAULT '',
    aadhaar_name    TEXT  NOT NULL DEFAULT '',
    aadhaar_dob     TEXT  NOT NULL DEFAULT '',
    aadhaar_gender  TEXT  NOT NULL DEFAULT '',
    aadhaar_father  TEXT  NOT NULL DEFAULT '',
    aadhaar_address TEXT  NOT NULL DEFAULT '',
    status        TEXT    NOT NULL DEFAULT 'active' CHECK (status IN ('active','left')),
    left_date     TEXT    NOT NULL DEFAULT '',
    left_note     TEXT    NOT NULL DEFAULT '',
    created_at    TEXT    NOT NULL,
    updated_at    TEXT    NOT NULL
);
CREATE TRIGGER IF NOT EXISTS trg_renter_id_locked
BEFORE UPDATE OF id ON renters
BEGIN
    SELECT RAISE(ABORT, 'A renter ID can never be changed');
END;
CREATE TABLE IF NOT EXISTS links (
    a_id       INTEGER NOT NULL REFERENCES renters(id) ON DELETE CASCADE,
    b_id       INTEGER NOT NULL REFERENCES renters(id) ON DELETE CASCADE,
    relation   TEXT    NOT NULL DEFAULT 'Roommate',
    created_at TEXT    NOT NULL,
    PRIMARY KEY (a_id, b_id),
    CHECK (a_id < b_id)
);
CREATE TABLE IF NOT EXISTS dues (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    renter_id  INTEGER NOT NULL REFERENCES renters(id) ON DELETE CASCADE,
    reason     TEXT    NOT NULL DEFAULT 'Overdue rent',
    amount     REAL    NOT NULL,
    due_date   TEXT    NOT NULL DEFAULT '',
    created_at TEXT    NOT NULL,
    status     TEXT    NOT NULL DEFAULT 'pending' CHECK (status IN ('pending','cleared')),
    cleared_at TEXT    NOT NULL DEFAULT ''
);
CREATE TABLE IF NOT EXISTS bills (
    id            INTEGER PRIMARY KEY AUTOINCREMENT,
    renter_id     INTEGER NOT NULL REFERENCES renters(id) ON DELETE CASCADE,
    created_at    TEXT    NOT NULL,
    primary_unit  REAL    NOT NULL DEFAULT 0,
    main_unit     REAL    NOT NULL DEFAULT 0,
    units         REAL    NOT NULL DEFAULT 0,
    unit_rate     REAL    NOT NULL DEFAULT 0,
    rent          REAL    NOT NULL DEFAULT 0,
    electricity   REAL    NOT NULL DEFAULT 0,
    wifi_fee      REAL    NOT NULL DEFAULT 0,
    back_dues     REAL    NOT NULL DEFAULT 0,
    advance       REAL    NOT NULL DEFAULT 0,
    subtotal      REAL    NOT NULL DEFAULT 0,
    note          TEXT    NOT NULL DEFAULT '',
    note_included INTEGER NOT NULL DEFAULT 0,
    sent_via      TEXT    NOT NULL DEFAULT '',
    has_reading   INTEGER NOT NULL DEFAULT 1,
    paid          INTEGER NOT NULL DEFAULT 0,
    paid_at       TEXT    NOT NULL DEFAULT '',
    message       TEXT    NOT NULL DEFAULT ''
);
CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE INDEX IF NOT EXISTS idx_bills_renter ON bills(renter_id, id);
CREATE INDEX IF NOT EXISTS idx_dues_renter  ON dues(renter_id, status);
"""

RENTER_TEXT = ["name", "phone", "alt_phone", "father_name", "mother_name", "parent_phone",
               "room_no", "join_date", "notes", "photo_path",
               "aadhaar_front_path", "aadhaar_back_path", "aadhaar_number", "aadhaar_name",
               "aadhaar_dob", "aadhaar_gender", "aadhaar_father", "aadhaar_address"]
RENTER_NUM = ["monthly_rent", "wifi_fee", "unit_rate"]

# Columns added after the original release. Existing databases get these bolted on
# with ALTER TABLE the first time they're opened with the new code (see Database._migrate).
_NEW_RENTER_COLUMNS = ["aadhaar_front_path", "aadhaar_back_path", "aadhaar_number", "aadhaar_name",
                       "aadhaar_dob", "aadhaar_gender", "aadhaar_father", "aadhaar_address"]

_RENTER_SELECT = """
SELECT r.*,
  COALESCE((SELECT SUM(amount) FROM dues d WHERE d.renter_id = r.id AND d.status = 'pending'), 0) AS pending_dues,
  (SELECT COUNT(*)   FROM dues d  WHERE d.renter_id = r.id AND d.status = 'pending')              AS pending_count,
  (SELECT subtotal   FROM bills b WHERE b.renter_id = r.id ORDER BY b.id DESC LIMIT 1)            AS last_total,
  (SELECT created_at FROM bills b WHERE b.renter_id = r.id ORDER BY b.id DESC LIMIT 1)            AS last_bill_at,
  (SELECT paid       FROM bills b WHERE b.renter_id = r.id ORDER BY b.id DESC LIMIT 1)            AS last_paid,
  (SELECT COUNT(*)   FROM links l WHERE l.a_id = r.id OR l.b_id = r.id)                           AS link_count
FROM renters r
"""


class Database:
    def __init__(self, path: Path = DB_PATH):
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.path = Path(path)
        self.conn = sqlite3.connect(str(path))
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA foreign_keys = ON")
        self.conn.executescript(SCHEMA)
        self.conn.commit()
        self._migrate()

    def _migrate(self) -> None:
        """Bolts on columns added in later versions, and moves data from the old
        single-image aadhaar_path into the new aadhaar_front_path field."""
        existing = {row["name"] for row in self.all("PRAGMA table_info(renters)")}
        for col in _NEW_RENTER_COLUMNS:
            if col not in existing:
                self.run(f"ALTER TABLE renters ADD COLUMN {col} TEXT NOT NULL DEFAULT ''")
        if "aadhaar_path" in existing:
            self.run("UPDATE renters SET aadhaar_front_path = aadhaar_path "
                      "WHERE aadhaar_front_path = '' AND aadhaar_path != ''")
        self.conn.commit()

    # -- small helpers --------------------------------------------------------
    def all(self, sql: str, args=()) -> list:
        return self.conn.execute(sql, args).fetchall()

    def one(self, sql: str, args=()):
        return self.conn.execute(sql, args).fetchone()

    def run(self, sql: str, args=()):
        with self.conn:
            return self.conn.execute(sql, args)

    # -- settings -------------------------------------------------------------
    def get_setting(self, key: str, default: str = "") -> str:
        row = self.one("SELECT value FROM settings WHERE key = ?", (key,))
        return row[0] if row else default

    def set_setting(self, key: str, value) -> None:
        self.run("INSERT OR REPLACE INTO settings(key, value) VALUES (?, ?)", (key, str(value)))

    # -- renters --------------------------------------------------------------
    def new_id(self) -> int:
        used = {r[0] for r in self.all("SELECT id FROM renters")}
        free = [i for i in range(1000, 10000) if i not in used]
        if not free:
            raise RuntimeError("All 9,000 four-digit IDs are already in use.")
        return random.choice(free)

    def id_exists(self, rid: int) -> bool:
        return self.one("SELECT 1 FROM renters WHERE id = ?", (rid,)) is not None

    def create_renter(self, rid: int, d: dict) -> None:
        now = now_iso()
        vals = [str(d.get(k, "") or "") for k in RENTER_TEXT] + [float(d.get(k, 0) or 0) for k in RENTER_NUM]
        with self.conn:
            self.conn.execute(
                f"INSERT INTO renters (id, {', '.join(RENTER_TEXT + RENTER_NUM)}, status, created_at, updated_at) "
                f"VALUES (?, {', '.join('?' * (len(RENTER_TEXT) + len(RENTER_NUM)))}, 'active', ?, ?)",
                [rid] + vals + [now, now])

    def update_renter(self, rid: int, d: dict) -> None:
        """Updates every profile field. The ID is never part of the update (and a trigger enforces it)."""
        cols = RENTER_TEXT + RENTER_NUM
        vals = [str(d.get(k, "") or "") for k in RENTER_TEXT] + [float(d.get(k, 0) or 0) for k in RENTER_NUM]
        with self.conn:
            self.conn.execute(
                f"UPDATE renters SET {', '.join(c + ' = ?' for c in cols)}, updated_at = ? WHERE id = ?",
                vals + [now_iso(), rid])

    def update_defaults(self, rid: int, rent: float, wifi: float, rate: float) -> None:
        self.run("UPDATE renters SET monthly_rent=?, wifi_fee=?, unit_rate=?, updated_at=? WHERE id=?",
                 (rent, wifi, rate, now_iso(), rid))

    def get_renter(self, rid: int) -> dict | None:
        row = self.one(_RENTER_SELECT + " WHERE r.id = ?", (rid,))
        return dict(row) if row else None

    def list_renters(self) -> list[dict]:
        rows = self.all(_RENTER_SELECT + " ORDER BY (r.status = 'left'), r.name COLLATE NOCASE")
        return [dict(r) for r in rows]

    def set_status(self, rid: int, status: str, left_date: str = "", left_note: str = "") -> None:
        if status == "active":
            left_date = left_note = ""
        self.run("UPDATE renters SET status=?, left_date=?, left_note=?, updated_at=? WHERE id=?",
                 (status, left_date, left_note, now_iso(), rid))

    def delete_renter(self, rid: int) -> None:
        r = self.get_renter(rid)
        if not r:
            return
        self.run("DELETE FROM renters WHERE id = ?", (rid,))
        remove_data_file(r["photo_path"])
        remove_data_file(r["aadhaar_front_path"])
        remove_data_file(r["aadhaar_back_path"])

    # -- links ----------------------------------------------------------------
    def links_for(self, rid: int) -> list[dict]:
        rows = self.all(
            """SELECT CASE WHEN l.a_id = :i THEN l.b_id ELSE l.a_id END AS other_id,
                      l.relation, r.name, r.photo_path, r.status, r.room_no
               FROM links l
               JOIN renters r ON r.id = CASE WHEN l.a_id = :i THEN l.b_id ELSE l.a_id END
               WHERE l.a_id = :i OR l.b_id = :i
               ORDER BY r.name COLLATE NOCASE""", {"i": rid})
        return [dict(r) for r in rows]

    def set_links(self, rid: int, wanted: dict[int, str]) -> None:
        current = {l["other_id"]: l["relation"] for l in self.links_for(rid)}
        with self.conn:
            for other in set(current) - set(wanted):
                a, b = sorted((rid, other))
                self.conn.execute("DELETE FROM links WHERE a_id=? AND b_id=?", (a, b))
            for other, rel in wanted.items():
                if other == rid or not self.id_exists(other):
                    continue
                a, b = sorted((rid, other))
                if other not in current:
                    self.conn.execute("INSERT INTO links(a_id, b_id, relation, created_at) VALUES (?,?,?,?)",
                                      (a, b, rel, now_iso()))
                elif current[other] != rel:
                    self.conn.execute("UPDATE links SET relation=? WHERE a_id=? AND b_id=?", (rel, a, b))

    # -- dues -----------------------------------------------------------------
    def add_due(self, rid: int, reason: str, amount: float, due_date: str) -> None:
        self.run("INSERT INTO dues(renter_id, reason, amount, due_date, created_at) VALUES (?,?,?,?,?)",
                 (rid, reason.strip() or "Overdue", amount, due_date, now_iso()))

    def dues_for(self, rid: int) -> list[dict]:
        rows = self.all("SELECT * FROM dues WHERE renter_id=? ORDER BY (status='cleared'), due_date DESC, id DESC", (rid,))
        return [dict(r) for r in rows]

    def set_due_status(self, due_id: int, status: str) -> None:
        self.run("UPDATE dues SET status=?, cleared_at=? WHERE id=?",
                 (status, now_iso() if status == "cleared" else "", due_id))

    def delete_due(self, due_id: int) -> None:
        self.run("DELETE FROM dues WHERE id=?", (due_id,))

    def pending_total(self, rid: int) -> float:
        row = self.one("SELECT COALESCE(SUM(amount),0) FROM dues WHERE renter_id=? AND status='pending'", (rid,))
        return float(row[0])

    def clear_all_pending(self, rid: int) -> None:
        self.run("UPDATE dues SET status='cleared', cleared_at=? WHERE renter_id=? AND status='pending'",
                 (now_iso(), rid))

    # -- bills ----------------------------------------------------------------
    def add_bill(self, rid: int, b: dict, message: str, sent_via: str) -> int:
        cur = self.run(
            """INSERT INTO bills (renter_id, created_at, primary_unit, main_unit, units, unit_rate, rent,
                                  electricity, wifi_fee, back_dues, advance, subtotal, note, note_included,
                                  sent_via, has_reading, message)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (rid, now_iso(), b["primary_unit"], b["main_unit"], b["units"], b["unit_rate"], b["rent"],
             b["electricity"], b["wifi_fee"], b["back_dues"], b["advance"], b["subtotal"], b.get("note", ""),
             1 if b.get("include_note") else 0, sent_via, 1 if b.get("has_reading") else 0, message))
        return int(cur.lastrowid)

    def bills_for(self, rid: int, limit: int | None = None) -> list[dict]:
        sql = "SELECT * FROM bills WHERE renter_id=? ORDER BY id DESC"
        if limit:
            sql += f" LIMIT {int(limit)}"
        return [dict(r) for r in self.all(sql, (rid,))]

    def bill_count(self, rid: int) -> int:
        return int(self.one("SELECT COUNT(*) FROM bills WHERE renter_id=?", (rid,))[0])

    def last_bill(self, rid: int) -> dict | None:
        row = self.one("SELECT * FROM bills WHERE renter_id=? ORDER BY id DESC LIMIT 1", (rid,))
        return dict(row) if row else None

    def set_bill_paid(self, bill_id: int, paid: bool) -> None:
        self.run("UPDATE bills SET paid=?, paid_at=? WHERE id=?", (1 if paid else 0, now_iso() if paid else "", bill_id))

    # -- dashboard ------------------------------------------------------------
    def stats(self) -> dict:
        month = datetime.now().strftime("%Y-%m")
        one = self.one
        return dict(
            active=one("SELECT COUNT(*) FROM renters WHERE status='active'")[0],
            left=one("SELECT COUNT(*) FROM renters WHERE status='left'")[0],
            billed=float(one("SELECT COALESCE(SUM(subtotal),0) FROM bills WHERE substr(created_at,1,7)=?", (month,))[0]),
            billed_n=one("SELECT COUNT(*) FROM bills WHERE substr(created_at,1,7)=?", (month,))[0],
            collected=float(one("SELECT COALESCE(SUM(subtotal),0) FROM bills WHERE paid=1 AND substr(created_at,1,7)=?", (month,))[0]),
            dues=float(one("SELECT COALESCE(SUM(amount),0) FROM dues WHERE status='pending'")[0]),
            dues_n=one("SELECT COUNT(DISTINCT renter_id) FROM dues WHERE status='pending'")[0],
        )


# ════════════════════════════════════════════════════════════════════════════
#  Files & pictures
# ════════════════════════════════════════════════════════════════════════════
def abs_data(rel: str) -> str:
    return str(DATA_DIR / rel) if rel else ""


def remove_data_file(rel: str) -> None:
    try:
        if rel:
            p = DATA_DIR / rel
            if p.is_file():
                p.unlink()
    except Exception:
        pass


def store_image(src: str, folder: Path, rid: int, tag: str) -> str:
    """Copy an uploaded picture into the data folder (original bytes, original format)."""
    folder.mkdir(parents=True, exist_ok=True)
    ext = Path(src).suffix.lower() or ".png"
    dest = folder / f"{rid}_{tag}_{datetime.now():%Y%m%d%H%M%S%f}{ext}"
    shutil.copy2(src, dest)
    return dest.relative_to(DATA_DIR).as_posix()


def is_image(path: str) -> bool:
    try:
        return bool(path) and os.path.isfile(path) and QImageReader(path).canRead()
    except Exception:
        return False


def is_pdf(path: str) -> bool:
    return bool(path) and path.lower().endswith(".pdf") and os.path.isfile(path)


# ── Aadhaar: reading a PDF's pages, running OCR, and pulling out the fields ────────
def render_pdf_pages(pdf_path: str, max_pages: int = 2) -> list[str]:
    """Turns the first `max_pages` pages of a PDF into PNGs (for staging into the
    front/back drop zones, and for OCR). Returns [] if PyMuPDF isn't installed or
    the file can't be read."""
    if not PDF_AVAILABLE or not is_pdf(pdf_path):
        return []
    out: list[str] = []
    try:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        doc = fitz.open(pdf_path)
        try:
            for i in range(min(max_pages, doc.page_count)):
                pix = doc.load_page(i).get_pixmap(matrix=fitz.Matrix(2.2, 2.2))
                dest = CACHE_DIR / f"aadhaar_pdf_{datetime.now():%Y%m%d%H%M%S%f}_{i}.png"
                pix.save(str(dest))
                out.append(str(dest))
        finally:
            doc.close()
    except Exception:
        return out
    return out


def ocr_extract_text(paths: list[str]) -> str:
    """Runs OCR over one or more images and returns the combined text. Raises if the
    OCR engine isn't available so callers can tell 'not installed' apart from
    'found nothing'."""
    if not OCR_AVAILABLE:
        raise RuntimeError("OCR is not available (install pytesseract, Pillow and Tesseract).")
    chunks = []
    for p in paths:
        if not p or not os.path.isfile(p):
            continue
        try:
            img = PILImage.open(p)
            if img.mode != "L":
                img = img.convert("L")
            chunks.append(pytesseract.image_to_string(img, lang="eng"))
        except Exception:
            continue
    return "\n".join(chunks)


_AADHAAR_BOILERPLATE = (
    "government of india", "unique identification authority", "authority of india",
    "aadhaar", "uidai", "address", "male", "female", "transgender", "download date",
    "issue date", "print date", "dob", "date of birth", "www.", "help@", "मेरा आधार",
    "पहचान", "भारत सरकार", "गवर्नमेंट",
)


def parse_aadhaar_text(text: str) -> dict:
    """Best-effort extraction of the fields printed on an Aadhaar card. OCR text from
    a photographed ID is noisy, so this fills in whatever it can find with confidence
    and simply leaves the rest blank for the person to type in - it never guesses."""
    text = text or ""
    out = dict(number="", name="", dob="", gender="", father="", address="")

    m = re.search(r"\b(\d{4}\s?\d{4}\s?\d{4})\b", text)
    if m:
        out["number"] = format_aadhaar_number(m.group(1))

    m = re.search(r"(?:DOB|Date of Birth)\s*[:\-]?\s*(\d{2}[/\-]\d{2}[/\-]\d{4})", text, re.I)
    if not m:
        m = re.search(r"\b(\d{2}[/\-]\d{2}[/\-]\d{4})\b", text)
    if m:
        out["dob"] = m.group(1).replace("-", "/")

    m = re.search(r"\b(Male|Female|Transgender)\b", text, re.I)
    if m:
        out["gender"] = m.group(1).capitalize()

    m = re.search(r"(?:S\s*/?\s*O|D\s*/?\s*O|W\s*/?\s*O|C\s*/?\s*O)[:.]?\s*([A-Za-z][A-Za-z .]{1,60})", text, re.I)
    if m:
        out["father"] = re.sub(r"\s+", " ", m.group(1)).strip(" .")

    m = re.search(r"Address\s*[:\-]?\s*(.+?)(?:\n\s*\n|\Z)", text, re.I | re.S)
    if m:
        addr = re.sub(r"\s+", " ", m.group(1)).strip()
        addr = re.split(r"help@|www\.|1947", addr)[0].strip(" ,")
        if addr:
            out["address"] = addr

    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    for i, ln in enumerate(lines):
        if re.search(r"dob|date of birth", ln, re.I) or re.search(r"\d{2}[/\-]\d{2}[/\-]\d{4}", ln):
            for j in range(i - 1, max(-1, i - 3), -1):
                cand = lines[j]
                low = cand.lower()
                if any(b in low for b in _AADHAAR_BOILERPLATE):
                    continue
                if re.fullmatch(r"[A-Za-z][A-Za-z .]{1,50}", cand) and len(cand.split()) <= 5:
                    out["name"] = cand.strip()
                    break
            break
    return out


def format_aadhaar_number(raw: str) -> str:
    """1234123412 34 -> '1234 1234 1234'; anything that isn't 12 digits is left as-is
    (digits only), so a partially-typed number doesn't get mangled while editing."""
    d = re.sub(r"\D", "", raw or "")
    if len(d) == 12:
        return f"{d[0:4]} {d[4:8]} {d[8:12]}"
    return d


def mask_aadhaar_number(number: str) -> str:
    d = re.sub(r"\D", "", number or "")
    if len(d) != 12:
        return number or "\u2014"
    return f"XXXX XXXX {d[8:12]}"


_pm_cache: dict = {}


def cover_pixmap(path: str, w: int, h: int, radius: float, dpr: float = 2.0) -> QPixmap | None:
    """Picture cropped to fill w x h (logical px) with rounded corners; cached."""
    if not path or not os.path.isfile(path):
        return None
    key = (path, os.path.getmtime(path), w, h, round(radius, 1), round(dpr, 2))
    if key in _pm_cache:
        return _pm_cache[key]
    tw, th = int(w * dpr), int(h * dpr)
    reader = QImageReader(path)
    reader.setAutoTransform(True)          # respects phone-camera rotation
    size = reader.size()
    if size.isValid() and size.width() > 0 and size.height() > 0:
        scale = max(tw / size.width(), th / size.height())
        if scale < 1:
            reader.setScaledSize(QSize(max(1, math.ceil(size.width() * scale)), max(1, math.ceil(size.height() * scale))))
    img = reader.read()
    if img.isNull():
        return None
    src = QPixmap.fromImage(img).scaled(tw, th, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                        Qt.TransformationMode.SmoothTransformation)
    out = QPixmap(tw, th)
    out.fill(Qt.GlobalColor.transparent)
    p = QPainter(out)
    p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
    p.setPen(Qt.PenStyle.NoPen)
    off = QPointF((tw - src.width()) / 2, (th - src.height()) / 2)
    brush = QBrush(src)
    from PyQt6.QtGui import QTransform
    brush.setTransform(QTransform.fromTranslate(off.x(), off.y()))
    p.setBrush(brush)
    p.drawRoundedRect(QRectF(0, 0, tw, th), radius * dpr, radius * dpr)
    p.end()
    out.setDevicePixelRatio(dpr)
    if len(_pm_cache) > 120:
        _pm_cache.clear()
    _pm_cache[key] = out
    return out


def load_pixmap(path: str, max_side: int = 2400) -> QPixmap | None:
    if not path or not os.path.isfile(path):
        return None
    reader = QImageReader(path)
    reader.setAutoTransform(True)
    size = reader.size()
    if size.isValid() and max(size.width(), size.height()) > max_side:
        size.scale(max_side, max_side, Qt.AspectRatioMode.KeepAspectRatio)
        reader.setScaledSize(size)
    img = reader.read()
    return None if img.isNull() else QPixmap.fromImage(img)


def avatar_colors(rid: int) -> tuple[QColor, QColor]:
    """Soft tint background + deeper text colour, derived from the renter ID."""
    hue = ((rid or 0) * 47 % 360) / 360.0
    if Theme.dark():
        return QColor.fromHslF(hue, 0.35, 0.24), QColor.fromHslF(hue, 0.75, 0.78)
    return QColor.fromHslF(hue, 0.60, 0.90), QColor.fromHslF(hue, 0.55, 0.30)


def draw_avatar(p: QPainter, rect: QRectF, d: dict, dpr: float = 2.0, dim: bool = False) -> None:
    """Squircle avatar: photo if there is one, otherwise tinted initials."""
    radius = rect.width() * 0.30
    p.save()
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    if dim:
        p.setOpacity(p.opacity() * 0.55)
    pm = cover_pixmap(abs_data(d.get("photo_path", "")), int(rect.width()), int(rect.height()), radius, dpr)
    if pm is not None:
        p.drawPixmap(QPointF(rect.x(), rect.y()), pm)
    else:
        bg, fg = avatar_colors(int(d.get("id") or 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(bg)
        p.drawRoundedRect(rect, radius, radius)
        p.setPen(fg)
        p.setFont(font(max(11, int(rect.width() * 0.36)), W_SEMI, display=True))
        p.drawText(rect, Qt.AlignmentFlag.AlignCenter, initials(d.get("name", "")))
    p.restore()


# ════════════════════════════════════════════════════════════════════════════
#  Export - "Fetch data" ZIP
# ════════════════════════════════════════════════════════════════════════════
def build_details_text(db: Database, rid: int) -> str:
    r = db.get_renter(rid)
    if not r:
        return ""
    W = 62
    out: list[str] = []

    def kv(k, v):
        out.append(f"  {k:<24}: {v if str(v).strip() not in ('', 'None') else '-'}")

    def head(t):
        out.extend(["", t, "-" * W])

    out += ["=" * W, f"  RENTER PROFILE  -  {r['name']}", "=" * W]
    head("PROFILE")
    kv("Renter ID", f"{r['id']}   (permanent, cannot be changed)")
    kv("Name", r["name"])
    kv("Status", "Active" if r["status"] == "active" else f"Left on {pretty_date(r['left_date'])}")
    if r["status"] == "left":
        kv("Reason / note", r["left_note"])
    kv("Room number", r["room_no"])
    kv("Joined on", pretty_date(r["join_date"]) if r["join_date"] else "")
    head("CONTACT")
    kv("Phone", r["phone"])
    kv("Alternate phone", r["alt_phone"])
    kv("Father's name", r["father_name"])
    kv("Mother's name", r["mother_name"])
    kv("Parent/guardian phone", r["parent_phone"])
    head("BILLING DEFAULTS")
    kv("Monthly rent", inr(r["monthly_rent"]))
    kv("WiFi fee", inr(r["wifi_fee"]))
    kv("One unit charge", inr(r["unit_rate"]))
    head("LINKED RENTERS")
    links = db.links_for(rid)
    if links:
        for l in links:
            out.append(f"  - {l['name']}  (ID {l['other_id']})  -  {l['relation']}"
                       + ("  [left]" if l["status"] == "left" else ""))
    else:
        out.append("  -")
    head("DUES / OVERDUE")
    dues = db.dues_for(rid)
    if dues:
        for d in dues:
            tag = "PENDING" if d["status"] == "pending" else "CLEARED"
            out.append(f"  [{tag}] {pretty_date(d['due_date'])}  {d['reason']}  -  {inr(d['amount'])}")
        out.append(f"  Pending total: {inr(db.pending_total(rid))}")
    else:
        out.append("  -")
    head("BILL HISTORY (newest first)")
    bills = db.bills_for(rid)
    if bills:
        for b in bills:
            out.append(f"  Bill #{b['id']}   {pretty_dt(b['created_at'])}   [{'PAID' if b['paid'] else 'UNPAID'}]")
            if b["has_reading"]:
                out.append(f"      Meter          : {num(b['primary_unit'])} -> {num(b['main_unit'])}  "
                           f"({num(b['units'])} units x {inr(b['unit_rate'])})")
            out.append(f"      Rent           : {inr(b['rent'])}")
            out.append(f"      Electricity    : {inr(b['electricity'])}")
            out.append(f"      WiFi           : {inr(b['wifi_fee'])}")
            out.append(f"      Back dues      : {inr(b['back_dues'])}")
            out.append(f"      Advance paid   : {inr(b['advance'])}")
            out.append(f"      TOTAL          : {inr(b['subtotal'])}")
            if b["note"]:
                out.append(f"      Note           : {b['note']}")
            out.append("")
    else:
        out.append("  -")
    head("NOTES")
    out.append("  " + (r["notes"].strip().replace("\n", "\n  ") if r["notes"].strip() else "-"))
    head("AADHAAR CARD")
    if r["aadhaar_number"] or r["aadhaar_name"] or r["aadhaar_front_path"] or r["aadhaar_back_path"]:
        kv("Aadhaar number", r["aadhaar_number"] or "-")
        kv("Name on card", r["aadhaar_name"] or "-")
        kv("DOB on card", r["aadhaar_dob"] or "-")
        kv("Gender on card", r["aadhaar_gender"] or "-")
        kv("Father's / guardian's name", r["aadhaar_father"] or "-")
        kv("Address on card", r["aadhaar_address"] or "-")
    else:
        out.append("  -")
    head("FILES IN THIS ARCHIVE")
    kv("Profile photo", "included" if r["photo_path"] and (DATA_DIR / r["photo_path"]).is_file() else "not uploaded")
    kv("Aadhaar card (front)", "included" if r["aadhaar_front_path"] and (DATA_DIR / r["aadhaar_front_path"]).is_file() else "not uploaded")
    kv("Aadhaar card (back)", "included" if r["aadhaar_back_path"] and (DATA_DIR / r["aadhaar_back_path"]).is_file() else "not uploaded")
    out += ["", f"Exported on {datetime.now():%d %b %Y, %I:%M %p} by {APP_NAME}", ""]
    return "\n".join(out)


def export_zip(db: Database, rids: list[int], dest: str) -> int:
    """One folder per renter: details.txt + profile photo + Aadhaar card (originals, skipped if missing)."""
    count = 0
    with zipfile.ZipFile(dest, "w", zipfile.ZIP_DEFLATED) as zf:
        summary = [f"{APP_NAME} export - {datetime.now():%d %b %Y, %I:%M %p}", ""]
        for rid in rids:
            r = db.get_renter(rid)
            if not r:
                continue
            folder = f"{safe_name(r['name'])}_{rid}"
            zf.writestr(f"{folder}/details.txt", build_details_text(db, rid).encode("utf-8-sig"))
            for key, base in (("photo_path", "profile_photo"), ("aadhaar_front_path", "aadhaar_card_front"),
                              ("aadhaar_back_path", "aadhaar_card_back")):
                rel = r[key]
                if rel and (DATA_DIR / rel).is_file():
                    zf.write(DATA_DIR / rel, f"{folder}/{base}{Path(rel).suffix.lower()}")
            summary.append(f"{rid}  {r['name']}  ({'active' if r['status'] == 'active' else 'left'})  room {r['room_no'] or '-'}")
            count += 1
        if len(rids) > 1:
            zf.writestr("ALL_RENTERS.txt", "\n".join(summary).encode("utf-8-sig"))
    return count


def reveal_in_folder(path: str) -> None:
    try:
        if sys.platform.startswith("win"):
            subprocess.Popen(["explorer", f"/select,{os.path.normpath(path)}"])
        elif sys.platform == "darwin":
            subprocess.Popen(["open", "-R", path])
        else:
            subprocess.Popen(["xdg-open", os.path.dirname(path)])
    except Exception:
        pass


def open_folder(path: str) -> None:
    QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))


# ════════════════════════════════════════════════════════════════════════════
#  Animation helpers
# ════════════════════════════════════════════════════════════════════════════
AL = Qt.AlignmentFlag
A_LEFT = AL.AlignLeft | AL.AlignVCenter
A_RIGHT = AL.AlignRight | AL.AlignVCenter
A_CENTER = AL.AlignCenter
EASE_OUT = QEasingCurve.Type.OutCubic
EASE_IN = QEasingCurve.Type.InCubic
EASE_INOUT = QEasingCurve.Type.InOutCubic


def fprop(name: str, default: float = 0.0):
    """A float Qt property that repaints the widget when it changes (so it can be animated)."""
    attr = "_p_" + name

    def getter(self):
        return getattr(self, attr, default)

    def setter(self, v):
        setattr(self, attr, v)
        self.update()
    return pyqtProperty(float, getter, setter)


class Animated:
    """Mixin: self._a('hv', 1.0, 160) animates the float property `hv` to 1.0."""

    def _a(self, prop: str, end: float, ms: int = 180, curve=EASE_OUT):
        m = self.__dict__.setdefault("_amap", {})
        a = m.get(prop)
        if a is None:
            a = QPropertyAnimation(self, prop.encode(), self)
            m[prop] = a
        a.stop()
        if not Motion.on or ms <= 0:
            setattr(self, prop, end)
            return a
        a.setDuration(ms)
        a.setEasingCurve(curve)
        a.setStartValue(getattr(self, prop))
        a.setEndValue(end)
        a.start()
        return a


def _drop_fx(w: QWidget, token=None):
    try:
        if token is None or getattr(w, "_fx_token", None) is token:
            w.setGraphicsEffect(None)
    except RuntimeError:
        pass


def fade_in(w: QWidget, ms: int = 260, delay: int = 0, dy: int = 0, done=None):
    """Fade (and optionally rise by `dy` px) a widget in. Works for widgets inside layouts."""
    if not Motion.on:
        if done:
            done()
        return
    token = object()
    w._fx_token = token
    eff = QGraphicsOpacityEffect(w)
    eff.setOpacity(0.0)
    w.setGraphicsEffect(eff)

    def start():
        try:
            group = QParallelAnimationGroup(w)
            a = QPropertyAnimation(eff, b"opacity", group)
            a.setDuration(ms)
            a.setStartValue(0.0)
            a.setEndValue(1.0)
            a.setEasingCurve(EASE_OUT)
            group.addAnimation(a)
            if dy:
                end = w.pos()
                pa = QPropertyAnimation(w, b"pos", group)
                pa.setDuration(ms + 120)
                pa.setStartValue(end + QPoint(0, dy))
                pa.setEndValue(end)
                pa.setEasingCurve(QEasingCurve.Type.OutQuint)
                group.addAnimation(pa)
                w.move(end + QPoint(0, dy))

            def finish():
                QTimer.singleShot(0, lambda: _drop_fx(w, token))
                if done:
                    done()
            group.finished.connect(finish)
            group.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)
        except RuntimeError:
            pass
    if delay > 0:
        QTimer.singleShot(delay, start)
    else:
        start()


def fade_out(w: QWidget, ms: int = 160, done=None):
    if not Motion.on:
        if done:
            done()
        return
    token = object()
    w._fx_token = token
    eff = QGraphicsOpacityEffect(w)
    eff.setOpacity(1.0)
    w.setGraphicsEffect(eff)
    a = QPropertyAnimation(eff, b"opacity", w)
    a.setDuration(ms)
    a.setStartValue(1.0)
    a.setEndValue(0.0)
    a.setEasingCurve(EASE_IN)

    def finish():
        if done:
            done()
        QTimer.singleShot(0, lambda: _drop_fx(w, token))
    a.finished.connect(finish)
    a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)


def shake(w: QWidget):
    """Quick horizontal shake - used to point at a field that needs attention."""
    if not Motion.on:
        return
    p = w.pos()
    a = QPropertyAnimation(w, b"pos", w)
    a.setDuration(380)
    for t, dx in ((0, 0), (0.14, -8), (0.3, 7), (0.46, -5), (0.62, 4), (0.8, -2), (1, 0)):
        a.setKeyValueAt(t, p + QPoint(dx, 0))
    a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)


def height_for(widget: QWidget, width: int) -> int:
    lay = widget.layout()
    if lay is not None:
        lay.activate()
        return lay.totalHeightForWidth(width) if lay.hasHeightForWidth() else lay.sizeHint().height()
    return widget.sizeHint().height()


# ════════════════════════════════════════════════════════════════════════════
#  Small building blocks
# ════════════════════════════════════════════════════════════════════════════
_TONE_KEY = {"text": "text", "text2": "text2", "text3": "text3", "green": "green_t",
             "amber": "amber_t", "red": "red_t", "blue": "blue", "on_ink": "on_ink"}


def _label_css(tone: str) -> str:
    # Deliberately a PER-INSTANCE stylesheet, never a global "QLabel { ... }" rule.
    # A global type-selector for QLabel makes Qt composite every label against the
    # top-level window instead of its immediate (custom-painted) parent, punching a
    # "hole" through any rounded card/panel behind it. Scoping the rule to each
    # widget instance avoids that entirely. See DEV_NOTES at the end of this file.
    return f"background: transparent; color: {Theme.hex(_TONE_KEY.get(tone, 'text'))};"


def label(text: str = "", size: int = 14, weight=W_NORMAL, tone: str = "text", display: bool = False,
          wrap: bool = False, align=None, selectable: bool = False) -> QLabel:
    l = QLabel(text)
    l.setFont(font(size, weight, display))
    l.setProperty("tone", tone)
    l.setStyleSheet(_label_css(tone))
    l.setWordWrap(wrap)
    if align is not None:
        l.setAlignment(align)
    if selectable:
        l.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
    return l


def set_tone(l: QLabel, tone: str) -> None:
    l.setProperty("tone", tone)
    l.setStyleSheet(_label_css(tone))


def spacer(h: int = 0, w: int = 0) -> QWidget:
    s = QWidget()
    s.setFixedSize(w, h) if (w and h) else (s.setFixedHeight(h) if h else s.setFixedWidth(w))
    return s


class Ico(QWidget):
    """An icon that always uses the current theme colour."""

    def __init__(self, name: str, tone: str = "text3", size: int = 16, stroke: float = 2.0, parent=None):
        super().__init__(parent)
        self.name, self.tone, self.sz, self.stroke = name, tone, size, stroke
        self.setFixedSize(size, size)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)

    def paintEvent(self, e):
        p = QPainter(self)
        p.drawPixmap(0, 0, icon_pm(self.name, C(self.tone), self.sz, self.devicePixelRatioF(), self.stroke))


class Divider(QWidget):
    def __init__(self, vertical: bool = False, parent=None):
        super().__init__(parent)
        self.vertical = vertical
        if vertical:
            self.setFixedWidth(1)
        else:
            self.setFixedHeight(1)

    def paintEvent(self, e):
        QPainter(self).fillRect(self.rect(), C("line"))


class Panel(TFrame):
    """Rounded surface. Radius and fill are chosen per use, not one-size-fits-all."""

    def __init__(self, radius: float = 22, fill: str = "surface", border: bool = True, parent=None):
        super().__init__(parent)
        self.radius, self.fill, self.border = radius, fill, border

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        p.setBrush(C(self.fill))
        p.setPen(QPen(C("line"), 1) if self.border else Qt.PenStyle.NoPen)
        p.drawRoundedRect(r, self.radius, self.radius)


class IconTile(QWidget):
    def __init__(self, name: str, tone: str = "ink", size: int = 40, parent=None):
        super().__init__(parent)
        self.name, self.tone, self.sz = name, tone, size
        self.setFixedSize(size, size)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        col = C(self.tone)
        p.setBrush(C(self.tone, 0.13) if self.tone != "ink" else C("surface3"))
        p.drawRoundedRect(QRectF(self.rect()), self.sz * 0.3, self.sz * 0.3)
        ic = int(self.sz * 0.5)
        fg = col if self.tone != "ink" else C("text")
        p.drawPixmap(int((self.sz - ic) / 2), int((self.sz - ic) / 2),
                     icon_pm(self.name, fg, ic, self.devicePixelRatioF()))


class AvatarView(QWidget):
    clicked = pyqtSignal()

    def __init__(self, size: int = 48, parent=None, clickable: bool = False):
        super().__init__(parent)
        self.setFixedSize(size, size)
        self.d: dict = {}
        self.dim = False
        self.clickable = clickable
        if clickable:
            self.setCursor(Qt.CursorShape.PointingHandCursor)

    def set_renter(self, d: dict, dim: bool = False):
        self.d, self.dim = d, dim
        self.update()

    def mousePressEvent(self, e):
        if self.clickable and e.button() == Qt.MouseButton.LeftButton and self.d.get("photo_path"):
            self.clicked.emit()
        else:
            super().mousePressEvent(e)

    def paintEvent(self, e):
        p = QPainter(self)
        draw_avatar(p, QRectF(self.rect()), self.d, self.devicePixelRatioF(), self.dim)


TONES = {  # tone -> (fill colour, text colour)
    "green": ("green", "green_t"), "amber": ("amber", "amber_t"), "red": ("red", "red_t"),
    "slate": ("slate", "text2"), "blue": ("blue", "blue"),
}


class Pill(QWidget):
    def __init__(self, text: str, tone: str = "slate", icon: str | None = None, size: int = 12,
                 outlined: bool = False, display: bool = False, parent=None):
        super().__init__(parent)
        self.text_, self.tone, self.icon_name, self.size_ = text, tone, icon, round(size)
        self.outlined, self.display = outlined, display
        self.setFont(font(self.size_, W_SEMI, display))
        self.setFixedHeight(self.size_ + 12)
        self.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        self.setFixedWidth(self.sizeHint().width())

    def set_text(self, t: str):
        self.text_ = t
        self.setFixedWidth(self.sizeHint().width())
        self.update()

    def sizeHint(self):
        fm = QFontMetrics(self.font())
        w = fm.horizontalAdvance(self.text_) + 20
        if self.icon_name:
            w += self.size_ + 2
        return QSize(w, self.size_ + 12)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        if self.tone == "ink":
            bg, fg, bd = C("ink"), C("on_ink"), None
        elif self.outlined:
            bg, fg, bd = QColor(0, 0, 0, 0), C("text2"), C("line2")
        else:
            fill, txt = TONES[self.tone]
            bg, fg, bd = C(fill, 0.15), C(txt), None
        p.setBrush(bg)
        p.setPen(QPen(bd, 1) if bd else Qt.PenStyle.NoPen)
        p.drawRoundedRect(r, r.height() / 2, r.height() / 2)
        x = r.left() + 10
        if self.icon_name:
            p.drawPixmap(QPointF(x - 1, r.center().y() - self.size_ / 2 + 0.5),
                         icon_pm(self.icon_name, fg, self.size_, self.devicePixelRatioF(), 2.2))
            x += self.size_ + 2
        p.setFont(self.font())
        p.setPen(fg)
        p.drawText(QRectF(x, r.top(), r.width(), r.height()), A_LEFT, self.text_)


# ════════════════════════════════════════════════════════════════════════════
#  Buttons
# ════════════════════════════════════════════════════════════════════════════
class Btn(Animated, QAbstractButton):
    """variants: ink | green | soft | ghost | danger | icon | link"""
    hv = fprop("hv")
    pr = fprop("pr")

    def __init__(self, text: str = "", variant: str = "ghost", icon: str | None = None,
                 size: str = "md", parent=None):
        super().__init__(parent)
        self.variant, self.icon_name, self.size_key = variant, icon, size
        self._h = {"sm": 34, "md": 42, "lg": 52}[size]
        self.setText(text)
        self.setFixedHeight(self._h)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.TabFocus)
        self.setFont(font({"sm": 13, "md": 14, "lg": 15}[size], W_SEMI))
        self.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)

    def set_icon(self, name):
        self.icon_name = name
        self.update()

    def set_variant(self, v):
        self.variant = v
        self.update()

    def sizeHint(self):
        t = self.text()
        if not t:
            return QSize(self._h, self._h)
        isz = 16 if self.size_key == "sm" else 18
        pad = {"sm": 14, "md": 18, "lg": 26}[self.size_key]
        w = QFontMetrics(self.font()).horizontalAdvance(t) + 2 * pad
        if self.icon_name:
            w += isz + 8
        return QSize(w, self._h)

    def minimumSizeHint(self):
        return self.sizeHint()

    def enterEvent(self, e):
        self._a("hv", 1.0, 140)

    def leaveEvent(self, e):
        self._a("hv", 0.0, 220)
        self._a("pr", 0.0, 120)

    def mousePressEvent(self, e):
        self._a("pr", 1.0, 80)
        super().mousePressEvent(e)

    def mouseReleaseEvent(self, e):
        self._a("pr", 0.0, 160)
        super().mouseReleaseEvent(e)

    def focusInEvent(self, e):
        super().focusInEvent(e)
        self.update()

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(1.5, 1.5, -1.5, -1.5)
        hv, pr, v = self.hv, self.pr, self.variant
        if not self.isEnabled():
            p.setOpacity(0.45)
        s = 1 - 0.03 * pr
        c = r.center()
        p.translate(c)
        p.scale(s, s)
        p.translate(-c.x(), -c.y())
        icon_only = not self.text()
        rad = r.height() / 2 if (icon_only or v == "green") else 13
        border = None
        if v == "ink":
            bg, fg = mix(C("ink"), C("ink_hi"), hv), C("on_ink")
        elif v == "green":
            bg, fg = mix(C("green"), C("green_hi"), hv), C("on_green")
        elif v == "soft":
            bg, fg = mix(C("surface3"), C("line2", 0.9), hv * 0.7), C("text")
        elif v == "danger":
            bg, fg = mix(C("red", 0.10), C("red", 0.20), hv), C("red_t")
        elif v == "icon":
            bg, fg = mix(C("surface3", 0.0), C("surface3"), hv), mix(C("text2"), C("text"), hv)
        elif v == "link":
            bg, fg = QColor(0, 0, 0, 0), mix(C("text2"), C("text"), hv)
        else:  # ghost
            bg, fg = mix(C("surface", 0.0), C("surface2"), hv), C("text")
            border = mix(C("line2"), C("text3"), hv)
        if self.hasFocus() and self.focusPolicy() != Qt.FocusPolicy.NoFocus:
            p.setPen(QPen(C("blue", 0.45), 3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(r.adjusted(-1, -1, 1, 1), rad + 1, rad + 1)
        p.setBrush(bg)
        p.setPen(QPen(border, 1.2) if border else Qt.PenStyle.NoPen)
        p.drawRoundedRect(r, rad, rad)
        t = self.text()
        isz = 16 if self.size_key == "sm" else 18
        fm = QFontMetrics(self.font())
        tw = fm.horizontalAdvance(t)
        total = tw + ((isz + (8 if t else 0)) if self.icon_name else 0)
        x = r.center().x() - total / 2
        if self.icon_name:
            p.drawPixmap(QPointF(x, r.center().y() - isz / 2),
                         icon_pm(self.icon_name, fg, isz, self.devicePixelRatioF(), 2.1))
            x += isz + (8 if t else 0)
        if t:
            p.setFont(self.font())
            p.setPen(fg)
            p.drawText(QRectF(x, r.top(), tw + 4, r.height()), A_LEFT, t)
        if v == "link" and hv > 0.01:
            p.setPen(QPen(fg, 1))
            y = r.center().y() + fm.ascent() / 2 + 2
            p.drawLine(QPointF(x, y), QPointF(x + tw, y))


class Switch(Animated, QAbstractButton):
    t = fprop("t")

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setCheckable(True)
        self.setFixedSize(48, 28)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.TabFocus)
        self.toggled.connect(lambda on: self._a("t", 1.0 if on else 0.0, 220, EASE_INOUT))

    def setChecked(self, on: bool):
        super().setChecked(on)
        self._a("t", 1.0 if on else 0.0, 0)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(2, 2, -2, -2)
        t = self.t
        if self.hasFocus():
            p.setPen(QPen(C("blue", 0.45), 3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(r.adjusted(-1, -1, 1, 1), r.height() / 2 + 1, r.height() / 2 + 1)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(mix(C("line2"), C("ink"), t))
        p.drawRoundedRect(r, r.height() / 2, r.height() / 2)
        kd = r.height() - 6
        stretch = 5 * math.sin(math.pi * t)          # knob squashes a little while it travels
        kx = r.left() + 3 + (r.width() - kd - 6) * t - (stretch if t > 0.5 else 0)
        p.setBrush(mix(QColor("#FFFFFF") if not Theme.dark() else C("text"), C("on_ink"), t))
        p.drawRoundedRect(QRectF(kx, r.top() + 3, kd + stretch, kd), kd / 2, kd / 2)


class Check(Animated, QAbstractButton):
    t = fprop("t")

    def __init__(self, text: str = "", parent=None):
        super().__init__(parent)
        self.setText(text)
        self.setCheckable(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.TabFocus)
        self.setFont(font(14, W_MED))
        self.setFixedHeight(28)
        self.toggled.connect(lambda on: self._a("t", 1.0 if on else 0.0, 200, EASE_OUT))

    def setChecked(self, on: bool):
        super().setChecked(on)
        self._a("t", 1.0 if on else 0.0, 0)

    def sizeHint(self):
        return QSize(22 + 10 + QFontMetrics(self.font()).horizontalAdvance(self.text()) + 4, 28)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        t = self.t
        box = QRectF(1, (self.height() - 22) / 2, 22, 22)
        if self.hasFocus():
            p.setPen(QPen(C("blue", 0.45), 3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(box.adjusted(-1, -1, 1, 1), 8, 8)
        p.setBrush(mix(C("surface"), C("ink"), t))
        p.setPen(QPen(mix(C("line2"), C("ink"), t), 1.4))
        p.drawRoundedRect(box.adjusted(0.7, 0.7, -0.7, -0.7), 7, 7)
        if t > 0.02:
            pts = [QPointF(box.x() + 5.5, box.y() + 11.5), QPointF(box.x() + 9.6, box.y() + 15.4),
                   QPointF(box.x() + 16.6, box.y() + 7.6)]
            path = QPainterPath(pts[0])
            seg1 = min(1.0, t / 0.45)
            path.lineTo(pts[0] + (pts[1] - pts[0]) * seg1)
            if t > 0.45:
                seg2 = (t - 0.45) / 0.55
                path.lineTo(pts[1] + (pts[2] - pts[1]) * seg2)
            pen = QPen(C("on_ink"), 2.3)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawPath(path)
        p.setFont(self.font())
        p.setPen(C("text"))
        p.drawText(QRectF(34, 0, self.width() - 34, self.height()), A_LEFT, self.text())


class Segmented(Animated, QWidget):
    changed = pyqtSignal(int)
    hx = fprop("hx")
    hw = fprop("hw")

    def __init__(self, items: list[str], parent=None):
        super().__init__(parent)
        self.items, self.idx = items, 0
        self.setFont(font(13, W_MED))
        fm = QFontMetrics(self.font())
        self.ws = [fm.horizontalAdvance(t) + 32 for t in items]
        self.setFixedSize(sum(self.ws) + 8, 42)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._p_hx, self._p_hw = 4.0, float(self.ws[0])

    def _x(self, i: int) -> float:
        return 4 + sum(self.ws[:i])

    def set_index(self, i: int, animate: bool = True, emit: bool = True):
        self.idx = i
        self._a("hx", self._x(i), 260 if animate else 0, QEasingCurve.Type.OutQuint)
        self._a("hw", float(self.ws[i]), 260 if animate else 0, QEasingCurve.Type.OutQuint)
        if emit:
            self.changed.emit(i)

    def mousePressEvent(self, e):
        x = e.position().x() - 4
        acc = 0
        for i, w in enumerate(self.ws):
            if acc <= x < acc + w:
                if i != self.idx:
                    self.set_index(i)
                return
            acc += w

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect())
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(C("surface3"))
        p.drawRoundedRect(r, 14, 14)
        pill = QRectF(self.hx, 4, self.hw, r.height() - 8)
        p.setBrush(C("surface"))
        p.setPen(QPen(C("line"), 1))
        p.drawRoundedRect(pill, 10, 10)
        p.setFont(self.font())
        for i, t in enumerate(self.items):
            cell = QRectF(self._x(i), 0, self.ws[i], r.height())
            overlap = max(0.0, 1 - abs(cell.center().x() - pill.center().x()) / max(1.0, cell.width()))
            p.setPen(mix(C("text2"), C("text"), overlap))
            p.drawText(cell, A_CENTER, t)


# ════════════════════════════════════════════════════════════════════════════
#  Inputs
# ════════════════════════════════════════════════════════════════════════════
class FieldFrame(Animated, TFrame):
    """Rounded input shell with an animated focus ring. Hosts any inner input widget."""
    fo = fprop("fo")
    hv = fprop("hv")
    er = fprop("er")

    def __init__(self, height: int = 46, parent=None):
        super().__init__(parent)
        self.setFixedHeight(height)
        self.leading_icon: str | None = None
        self._inners: list = []

    def _bind(self, w: QWidget):
        w.installEventFilter(self)
        self._inners.append(w)

    def eventFilter(self, o, ev):
        if o in self._inners:
            t = ev.type()
            if t == QEvent.Type.FocusIn:
                self._a("fo", 1.0, 150)
            elif t == QEvent.Type.FocusOut:
                self._a("fo", 0.0, 220)
        return False

    def enterEvent(self, e):
        self._a("hv", 1.0, 130)

    def leaveEvent(self, e):
        self._a("hv", 0.0, 200)

    def set_error(self, on: bool = True):
        self._a("er", 1.0 if on else 0.0, 150)
        if on:
            shake(self)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(2.5, 2.5, -2.5, -2.5)
        fo, er = self.fo, self.er
        if fo > 0.01:
            p.setPen(QPen(C("blue", 0.20 * fo), 4))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(r, 12, 12)
        border = mix(mix(C("line"), C("line2"), self.hv), C("blue"), fo)
        border = mix(border, C("red"), er)
        p.setPen(QPen(border, 1.0 + 0.5 * fo))
        p.setBrush(mix(C("surface2"), C("surface"), fo))
        p.drawRoundedRect(r, 12, 12)
        if self.leading_icon:
            p.drawPixmap(QPointF(15, (self.height() - 17) / 2),
                         icon_pm(self.leading_icon, mix(C("text3"), C("text2"), fo), 17, self.devicePixelRatioF()))


_VALIDATORS = {
    "money": r"^\d{0,9}(\.\d{0,2})?$",
    "units": r"^\d{0,9}(\.\d{0,3})?$",
    "phone": r"^[0-9+\-\s()]{0,20}$",
    "id": r"^\d{0,4}$",
    "aadhaar": r"^[\d ]{0,14}$",
}


class Field(FieldFrame):
    submitted = pyqtSignal()
    changed = pyqtSignal(str)

    def __init__(self, placeholder: str = "", icon: str | None = None, prefix: str = "", suffix: str = "",
                 kind: str = "text", multiline: bool = False, big: bool = False, parent=None):
        super().__init__(100 if multiline else (58 if big else 46), parent)
        self.leading_icon = icon
        self.multiline = multiline
        lay = QHBoxLayout(self)
        lay.setContentsMargins(42 if icon else 15, 0 if not multiline else 6, 14, 0 if not multiline else 6)
        lay.setSpacing(6)
        if prefix:
            lay.addWidget(label(prefix, 16 if big else 14, W_MED, "text3"))
        if multiline:
            self.edit = QPlainTextEdit()
            self.edit.setFrameShape(QFrame.Shape.NoFrame)
            self.edit.setTabChangesFocus(True)
            self.edit.viewport().setAutoFillBackground(False)
            self.edit.textChanged.connect(lambda: self.changed.emit(self.text()))
        else:
            self.edit = QLineEdit()
            self.edit.textChanged.connect(self.changed.emit)
            self.edit.returnPressed.connect(self.submitted.emit)
        # Per-instance stylesheet, deliberately not a global "QLineEdit {...}"/"QPlainTextEdit {...}"
        # rule - see the note on _label_css above; the same top-level-compositing issue applies to
        # any standard Qt input widget nested inside our custom-painted FieldFrame.
        self.edit.setStyleSheet(
            f"background: transparent; border: none; color: {Theme.hex('text')}; "
            f"selection-background-color: {Theme.hex('blue')}; selection-color: #ffffff; "
            f"placeholder-text-color: {Theme.hex('text3')};")
        self.edit.setFont(font(22 if big else 14, W_SEMI if big else W_NORMAL, display=big))
        self.edit.setPlaceholderText(placeholder)
        if kind in _VALIDATORS and not multiline:
            self.edit.setValidator(QRegularExpressionValidator(QRegularExpression(_VALIDATORS[kind]), self.edit))
        lay.addWidget(self.edit, 1)
        if suffix:
            lay.addWidget(label(suffix, 13, W_MED, "text3"))
        self._bind(self.edit)

    def text(self) -> str:
        return self.edit.toPlainText() if self.multiline else self.edit.text()

    def setText(self, s: str):
        (self.edit.setPlainText if self.multiline else self.edit.setText)(s or "")

    def value(self) -> float:
        return to_float(self.text())

    def setFocus(self, *a):
        self.edit.setFocus(*a)


class DateField(FieldFrame):
    def __init__(self, parent=None):
        super().__init__(46, parent)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(15, 0, 8, 0)
        self.de = QDateEdit(QDate.currentDate())
        self.de.setCalendarPopup(True)
        self.de.setDisplayFormat("dd MMM yyyy")
        self.de.setFont(font(14))
        # Per-instance (see the note in Field.__init__) - a global "QDateEdit {...}" rule would
        # punch the same hole through this FieldFrame's rounded background.
        chev = icon_file("chevron-down", Theme.hex("text2"), 14)
        self.de.setStyleSheet(
            f"QDateEdit {{ background: transparent; border: none; color: {Theme.hex('text')}; padding: 0; "
            f"selection-background-color: {Theme.hex('blue')}; selection-color: #ffffff; }} "
            f"QDateEdit::drop-down {{ border: none; width: 26px; subcontrol-origin: padding; "
            f"subcontrol-position: center right; }} "
            f"QDateEdit::down-arrow {{ image: url({chev}); width: 14px; height: 14px; }}")
        lay.addWidget(self.de)
        self._bind(self.de)
        if self.de.lineEdit() is not None:
            self._bind(self.de.lineEdit())
        cal = self.de.calendarWidget()
        if cal is not None:
            cal.setStyleSheet(_calendar_css())

    def iso(self) -> str:
        return self.de.date().toString("yyyy-MM-dd")

    def set_iso(self, s: str):
        d = QDate.fromString((s or "")[:10], "yyyy-MM-dd")
        self.de.setDate(d if d.isValid() else QDate.currentDate())


class Select(FieldFrame):
    changed = pyqtSignal(str)

    def __init__(self, options: list[str], current: str | None = None, parent=None):
        super().__init__(46, parent)
        self.options = list(options)
        self.val = current if current in options else options[0]
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setFont(font(14))
        self._bind(self)

    def value(self) -> str:
        return self.val

    def set_value(self, v: str):
        if v in self.options:
            self.val = v
            self.update()

    def mousePressEvent(self, e):
        self.open_menu()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_Space, Qt.Key.Key_Return, Qt.Key.Key_Enter, Qt.Key.Key_Down):
            self.open_menu()
        else:
            super().keyPressEvent(e)

    def open_menu(self):
        m = QMenu(self)
        m.setWindowFlags(m.windowFlags() | Qt.WindowType.FramelessWindowHint | Qt.WindowType.NoDropShadowWindowHint)
        m.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        blank = QPixmap(1, 1)
        blank.fill(Qt.GlobalColor.transparent)
        tick = icon_pm("check", C("text"), 16, self.devicePixelRatioF(), 2.4)
        for o in self.options:
            a = m.addAction(QIcon(tick if o == self.val else blank), o)
            a.setData(o)
        m.setMinimumWidth(self.width())
        chosen = m.exec(self.mapToGlobal(QPoint(0, self.height() + 4)))
        if chosen is not None and chosen.data() != self.val:
            self.val = chosen.data()
            self.update()
            self.changed.emit(self.val)

    def paintEvent(self, e):
        super().paintEvent(e)
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setFont(self.font())
        p.setPen(C("text"))
        p.drawText(QRectF(15, 0, self.width() - 50, self.height()), A_LEFT, self.val)
        p.drawPixmap(QPointF(self.width() - 31, (self.height() - 16) / 2),
                     icon_pm("chevron-down", C("text2"), 16, self.devicePixelRatioF(), 2.2))


def labeled(text: str, widget: QWidget, hint: str = "") -> QWidget:
    w = TWidget()
    l = QVBoxLayout(w)
    l.setContentsMargins(0, 0, 0, 0)
    l.setSpacing(7)
    l.addWidget(label(text, 13, W_MED, "text2"))
    l.addWidget(widget)
    if hint:
        l.addWidget(label(hint, 12, W_NORMAL, "text3", wrap=True))
    return w


# ════════════════════════════════════════════════════════════════════════════
#  Motion widgets
# ════════════════════════════════════════════════════════════════════════════
class AnimatedNumber(QLabel):
    def __init__(self, fmt=inr, size: int = 24, weight=W_SEMI, tone: str = "text", display: bool = True, parent=None):
        super().__init__("", parent)
        self.setFont(font(size, weight, display))
        self.setProperty("tone", tone)
        self.fmt, self._v = fmt, 0.0
        self._anim = QVariantAnimation(self)
        self._anim.valueChanged.connect(self._tick)
        self.setText(fmt(0))

    def _tick(self, v):
        self._v = float(v)
        self.setText(self.fmt(self._v))

    def set_value(self, v: float, animate: bool = True):
        self._anim.stop()
        if not animate or not Motion.on or abs(float(v) - self._v) < 0.005:
            self._tick(v)
            return
        self._anim.setDuration(520)
        self._anim.setEasingCurve(EASE_OUT)
        self._anim.setStartValue(float(self._v))
        self._anim.setEndValue(float(v))
        self._anim.start()


class Collapsible(QWidget):
    """Height-animated container - used for 'Advanced options' and the message preview."""

    def __init__(self, content: QWidget, parent=None):
        super().__init__(parent)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.addWidget(content)
        self.content = content
        self._t = 0.0
        self.is_open = False
        self.content.setVisible(False)
        self.setMaximumHeight(0)
        self._anim = QPropertyAnimation(self, b"prog", self)

    def _get(self):
        return self._t

    def _set(self, v):
        self._t = v
        if v <= 0.001:
            self.setMaximumHeight(0)
            self.content.setVisible(False)
        elif v >= 0.999:
            self.setMaximumHeight(16777215)
        else:
            self.setMaximumHeight(int(height_for(self.content, max(self.width(), 200)) * v))

    prog = pyqtProperty(float, _get, _set)

    def set_open(self, on: bool, animate: bool = True):
        self.is_open = on
        self._anim.stop()
        if on:
            self.content.setVisible(True)
        if not animate or not Motion.on:
            self._set(1.0 if on else 0.0)
            return
        self._anim.setDuration(340 if on else 240)
        self._anim.setEasingCurve(QEasingCurve.Type.OutQuint if on else EASE_INOUT)
        self._anim.setStartValue(self._t)
        self._anim.setEndValue(1.0 if on else 0.0)
        self._anim.start()


# ════════════════════════════════════════════════════════════════════════════
#  Drop zone - click to browse or drag a picture in
# ════════════════════════════════════════════════════════════════════════════
class DropZone(Animated, QWidget):
    changed = pyqtSignal()
    pdf_chosen = pyqtSignal(str)   # emitted instead of `changed` when a PDF is dropped/picked
    hv = fprop("hv")
    dg = fprop("dg")
    pop = fprop("pop", 1.0)
    ph = fprop("ph")

    def __init__(self, title: str, hint: str, w: int, h: int, squircle: bool = False,
                 icon: str = "upload", accept_pdf: bool = False, parent=None):
        super().__init__(parent)
        self.title, self.hint, self.squircle, self.icon_name = title, hint, squircle, icon
        self.accept_pdf = accept_pdf
        self.setFixedSize(w, h)
        self.setAcceptDrops(True)
        self.setMouseTracking(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.rel = ""        # picture already stored for this renter (relative path)
        self.staged = ""     # newly chosen picture (absolute path), copied only when the profile is saved
        self.removed = False
        self._over_x = False
        self._march = QPropertyAnimation(self, b"ph", self)
        self._march.setDuration(800)
        self._march.setStartValue(0.0)
        self._march.setEndValue(10.0)
        self._march.setLoopCount(-1)
        self._march.setEasingCurve(QEasingCurve.Type.Linear)

    # -- state -----------------------------------------------------------------
    def load(self, rel: str):
        self.rel, self.staged, self.removed = rel or "", "", False
        self.update()

    def current_path(self) -> str:
        if self.staged:
            return self.staged
        return "" if self.removed else abs_data(self.rel)

    def has_image(self) -> bool:
        p = self.current_path()
        return bool(p) and os.path.isfile(p)

    def state(self) -> tuple[str, str]:
        if self.staged:
            return "new", self.staged
        if self.removed:
            return "remove", ""
        return "keep", self.rel

    def stage(self, path: str):
        if not is_image(path):
            self.window().toast("That file is not a picture we can open. Try a PNG or JPG.", "error")
            return
        self.staged, self.removed = path, False
        self._p_pop = 0.0
        self._a("pop", 1.0, 520, QEasingCurve.Type.OutBack)
        self.changed.emit()

    def clear_image(self):
        self.staged, self.removed = "", True
        self.update()
        self.changed.emit()

    def browse(self):
        start = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.PicturesLocation)
        filt = AADHAAR_FILTER if self.accept_pdf else IMAGE_FILTER
        path, _ = QFileDialog.getOpenFileName(self.window(), "Choose a picture", start, filt)
        if not path:
            return
        if self.accept_pdf and is_pdf(path):
            self.pdf_chosen.emit(path)
        else:
            self.stage(path)

    # -- events ------------------------------------------------------------------
    def _rect(self) -> QRectF:
        return QRectF(self.rect()).adjusted(2, 2, -2, -2)

    def _radius(self) -> float:
        return self._rect().width() * 0.30 if self.squircle else 22

    def _x_rect(self) -> QRectF:
        R = self._rect()
        return QRectF(R.right() - (40 if self.squircle else 42), R.top() + (12 if self.squircle else 12), 30, 30)

    def enterEvent(self, e):
        self._a("hv", 1.0, 150)

    def leaveEvent(self, e):
        self._a("hv", 0.0, 220)
        self._over_x = False

    def mouseMoveEvent(self, e):
        over = self.has_image() and self._x_rect().contains(QPointF(e.position()))
        if over != self._over_x:
            self._over_x = over
            self.update()

    def mousePressEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton:
            return
        if self.has_image() and self._x_rect().contains(QPointF(e.position())):
            self.clear_image()
        else:
            self.browse()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter, Qt.Key.Key_Space):
            self.browse()
        else:
            super().keyPressEvent(e)

    def _accepts(self, path: str) -> bool:
        return is_image(path) or (self.accept_pdf and is_pdf(path))

    def dragEnterEvent(self, e):
        md = e.mimeData()
        if md.hasUrls() and any(self._accepts(u.toLocalFile()) for u in md.urls()):
            e.acceptProposedAction()
            self._a("dg", 1.0, 180)
            self._march.start()
        else:
            e.ignore()

    def dragLeaveEvent(self, e):
        self._a("dg", 0.0, 220)
        self._march.stop()

    def dropEvent(self, e):
        self._a("dg", 0.0, 220)
        self._march.stop()
        for u in e.mimeData().urls():
            f = u.toLocalFile()
            if self.accept_pdf and is_pdf(f):
                e.acceptProposedAction()
                self.pdf_chosen.emit(f)
                return
            if is_image(f):
                e.acceptProposedAction()
                self.stage(f)
                return

    # -- painting ------------------------------------------------------------------
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
        R, rad = self._rect(), self._radius()
        act = max(self.hv, self.dg)
        dpr = self.devicePixelRatioF()
        if self.hasFocus():
            p.setPen(QPen(C("blue", 0.4), 3))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(R.adjusted(-1, -1, 1, 1), rad + 1, rad + 1)
        if self.has_image():
            s = 0.94 + 0.06 * self.pop
            p.save()
            c = R.center()
            p.translate(c)
            p.scale(s, s)
            p.translate(-c.x(), -c.y())
            p.setOpacity(min(1.0, 0.3 + 0.7 * self.pop))
            pm = cover_pixmap(self.current_path(), int(R.width()), int(R.height()), rad, dpr)
            if pm is not None:
                p.drawPixmap(R.topLeft(), pm)
            p.restore()
            p.setPen(QPen(C("line"), 1))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(R, rad, rad)
            if act > 0.01:
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(8, 10, 18, int(150 * act)))
                p.drawRoundedRect(R, rad, rad)
                white = QColor(255, 255, 255, int(255 * act))
                p.drawPixmap(QPointF(R.center().x() - 12, R.center().y() - 26),
                             icon_pm("camera", white, 24, dpr, 2.0))
                p.setPen(white)
                p.setFont(font(13, W_SEMI))
                p.drawText(QRectF(R.left(), R.center().y() + 6, R.width(), 24), A_CENTER,
                           "Release to replace" if self.dg > 0.5 else "Change picture")
                xr = self._x_rect()
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(255, 255, 255, int((250 if self._over_x else 225) * act)))
                p.drawEllipse(xr)
                p.drawPixmap(QPointF(xr.center().x() - 8, xr.center().y() - 8),
                             icon_pm("x", QColor(190, 40, 60) if self._over_x else QColor(20, 22, 30), 16, dpr, 2.4))
            return
        # empty state
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(mix(C("surface2"), C("blue", 0.08), act))
        p.drawRoundedRect(R, rad, rad)
        pen = QPen(mix(C("line2"), C("blue"), act), 1.6)
        pen.setStyle(Qt.PenStyle.CustomDashLine)
        pen.setDashPattern([4.0, 4.0])
        pen.setDashOffset(self.ph)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(R, rad, rad)
        cy = R.center().y() - (24 if self.squircle else 30)
        bump = 1 + 0.10 * act
        tile = 46 * bump
        tr = QRectF(R.center().x() - tile / 2, cy - tile / 2, tile, tile)
        p.setPen(QPen(mix(C("line"), C("blue", 0.4), act), 1))
        p.setBrush(C("surface"))
        p.drawRoundedRect(tr, 15, 15)
        p.drawPixmap(QPointF(tr.center().x() - 11, tr.center().y() - 11 - 2 * act),
                     icon_pm(self.icon_name, mix(C("text2"), C("blue"), act), 22, dpr, 2.0))
        p.setFont(font(14, W_SEMI))
        p.setPen(mix(C("text"), C("blue"), self.dg))
        p.drawText(QRectF(R.left() + 10, cy + 30, R.width() - 20, 24), A_CENTER,
                   "Release to upload" if self.dg > 0.5 else self.title)
        p.setFont(font(12))
        p.setPen(C("text3"))
        p.drawText(QRectF(R.left() + 10, cy + 54, R.width() - 20, 20), A_CENTER, self.hint)


class AadhaarOcrWorker(QThread):
    """Runs OCR off the UI thread so staging a photo never freezes the window."""
    done = pyqtSignal(dict)
    failed = pyqtSignal(str)

    def __init__(self, paths: list[str], parent=None):
        super().__init__(parent)
        self.paths = list(paths)

    def run(self):
        try:
            text = ocr_extract_text(self.paths)
            self.done.emit(parse_aadhaar_text(text))
        except Exception as e:
            self.failed.emit(str(e))


# ════════════════════════════════════════════════════════════════════════════
#  Overlays: dialog, side drawer, picture viewer
# ════════════════════════════════════════════════════════════════════════════
class Overlay(Animated, TWidget):
    closed = pyqtSignal()
    dm = fprop("dm")
    dim_alpha = 140

    def __init__(self, win, dismissable: bool = True):
        super().__init__(win)
        self.win = win
        self.dismissable = dismissable
        self._closing = False
        self._open = False
        self._moving = False
        self.setGeometry(win.rect())
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.hide()
        win.overlays.append(self)

    # subclass hooks
    def content_rect(self) -> QRectF:
        return QRectF()

    def layout_content(self):
        pass

    def animate_in(self):
        pass

    def animate_out(self, done):
        done()

    def paint_extra(self, p: QPainter):
        pass

    def after_open(self):
        pass

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.fillRect(self.rect(), QColor(8, 10, 18, int(self.dim_alpha * self.dm)))
        self.paint_extra(p)

    def resizeEvent(self, e):
        self.layout_content()

    def open(self):
        self.setGeometry(self.win.rect())
        self.show()
        self.raise_()
        self._open = True
        self.layout_content()
        self.setFocus()
        self._a("dm", 1.0, 280)
        self.animate_in()
        QTimer.singleShot(80, self.after_open)

    def dismiss(self, *_):
        if self._closing:
            return
        self._closing = True
        self._a("dm", 0.0, 230)
        self.animate_out(self._finish)

    def _finish(self):
        if self in self.win.overlays:
            self.win.overlays.remove(self)
        self.closed.emit()
        self.hide()
        self.deleteLater()

    def mousePressEvent(self, e):
        if self.dismissable and not self.content_rect().contains(QPointF(e.position())):
            self.dismiss()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape and self.dismissable:
            self.dismiss()
        else:
            super().keyPressEvent(e)


class DrawerPanel(TWidget):
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(QPen(C("line"), 1))
        p.setBrush(C("surface"))
        p.drawRoundedRect(QRectF(0.5, 0.5, self.width() + 40, self.height() - 1), 30, 30)


class Drawer(Overlay):
    """Sheet that slides in from the right."""

    def __init__(self, win, width: int = 500):
        super().__init__(win)
        self.dw = width
        self.panel = DrawerPanel(self)

    def content_rect(self):
        return QRectF(self.panel.geometry())

    def layout_content(self):
        w = min(self.dw, self.width())
        self.panel.resize(w, self.height())
        if not self._moving:
            self.panel.move(self.width() - w if (self._open and not self._closing) else self.width(), 0)

    def animate_in(self):
        w = self.panel.width()
        if not Motion.on:
            self.panel.move(self.width() - w, 0)
            return
        self._moving = True
        self.panel.move(self.width(), 0)
        a = QPropertyAnimation(self.panel, b"pos", self)
        a.setDuration(400)
        a.setStartValue(QPoint(self.width(), 0))
        a.setEndValue(QPoint(self.width() - w, 0))
        a.setEasingCurve(QEasingCurve.Type.OutQuint)
        a.valueChanged.connect(lambda *_: self.update())
        a.finished.connect(lambda: setattr(self, "_moving", False))
        a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)

    def animate_out(self, done):
        if not Motion.on:
            done()
            return
        self._moving = True
        a = QPropertyAnimation(self.panel, b"pos", self)
        a.setDuration(260)
        a.setStartValue(self.panel.pos())
        a.setEndValue(QPoint(self.width(), 0))
        a.setEasingCurve(EASE_IN)
        a.valueChanged.connect(lambda *_: self.update())
        a.finished.connect(done)
        a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)

    def paint_extra(self, p):
        x = self.panel.x()
        g = QLinearGradient(x - 46, 0, x, 0)
        g.setColorAt(0, QColor(8, 10, 18, 0))
        g.setColorAt(1, QColor(8, 10, 18, int(60 * self.dm)))
        p.fillRect(QRectF(x - 46, 0, 46, self.height()), g)


class Dialog(Overlay):
    """Centered dialog with a title, optional sub-title, a body and a button row."""

    def __init__(self, win, title: str, subtitle: str = "", width: int = 480):
        super().__init__(win)
        self.dw = width
        self.primary: Btn | None = None
        self.panel = Panel(28, "surface", True, self)
        self.v = QVBoxLayout(self.panel)
        self.v.setContentsMargins(32, 30, 32, 26)
        self.v.setSpacing(0)
        self.v.addWidget(label(title, 22, W_SEMI, display=True, wrap=True))
        if subtitle:
            self.v.addSpacing(8)
            self.v.addWidget(label(subtitle, 14, tone="text2", wrap=True))
        self.body = QVBoxLayout()
        self.body.setSpacing(16)
        self.body.setContentsMargins(0, 20, 0, 0)
        self.v.addLayout(self.body)
        self.buttons = QHBoxLayout()
        self.buttons.setSpacing(10)
        self.buttons.setContentsMargins(0, 26, 0, 0)
        self.buttons.addStretch()
        self.v.addLayout(self.buttons)

    def add_button(self, text: str, variant: str = "ghost", cb=None, close: bool = True, icon=None) -> Btn:
        b = Btn(text, variant, icon)
        self.buttons.addWidget(b)

        def go():
            if cb is not None:
                if cb() is False:
                    return
            if close:
                self.dismiss()
        b.clicked.connect(go)
        if variant in ("ink", "green", "danger") and self.primary is None:
            self.primary = b
        return b

    def content_rect(self):
        return QRectF(self.panel.geometry())

    def refit(self):
        w = min(self.dw, self.width() - 40)
        h = height_for(self.panel, w)
        self.panel.setFixedSize(w, h)
        if not self._moving:
            self.panel.move((self.width() - w) // 2, max(20, (self.height() - h) // 2 - 10))

    def layout_content(self):
        self.refit()

    def animate_in(self):
        end = self.panel.pos()
        if not Motion.on:
            return
        self._moving = True
        fade_in(self.panel, 220)
        a = QPropertyAnimation(self.panel, b"pos", self)
        a.setDuration(380)
        a.setStartValue(end + QPoint(0, 26))
        a.setEndValue(end)
        a.setEasingCurve(QEasingCurve.Type.OutQuint)
        a.valueChanged.connect(lambda *_: self.update())
        a.finished.connect(lambda: setattr(self, "_moving", False))
        self.panel.move(end + QPoint(0, 26))
        a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)

    def animate_out(self, done):
        if not Motion.on:
            done()
            return
        fade_out(self.panel, 170, done)

    def paint_extra(self, p):
        r = QRectF(self.panel.geometry())
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(14, 0, -1):
            p.setBrush(QColor(8, 10, 18, int(2.4 * self.dm * (15 - i) / 3)))
            p.drawRoundedRect(r.adjusted(-i, -i + 10, i, i + 10), 28 + i, 28 + i)

    def after_open(self):
        for w in self.panel.findChildren(QLineEdit):
            w.setFocus()
            break

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter) and self.primary is not None:
            fw = QApplication.focusWidget()
            if not isinstance(fw, (QPlainTextEdit, QAbstractButton)):
                self.primary.click()
                return
        super().keyPressEvent(e)


class Viewer(Overlay):
    """Full-window picture viewer. Click anywhere or press Esc to close."""
    dim_alpha = 215
    pp = fprop("pp", 0.0)

    def __init__(self, win, path: str, caption: str = ""):
        super().__init__(win)
        self.pm = load_pixmap(path, 2600)
        self.caption = caption

    def open(self):
        super().open()
        self._a("pp", 1.0, 420, QEasingCurve.Type.OutQuint)

    def dismiss(self, *_):
        self._a("pp", 0.0, 200)
        super().dismiss()

    def mousePressEvent(self, e):
        self.dismiss()

    def paint_extra(self, p):
        if self.pm is None:
            return
        avail = QSizeF_fit(self.width() - 120, self.height() - 150)
        scaled = self.pm.scaled(int(avail[0] * self.devicePixelRatioF()), int(avail[1] * self.devicePixelRatioF()),
                                Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
        scaled.setDevicePixelRatio(self.devicePixelRatioF())
        w, h = scaled.width() / self.devicePixelRatioF(), scaled.height() / self.devicePixelRatioF()
        s = 0.94 + 0.06 * self.pp
        p.save()
        p.setOpacity(min(1.0, self.pp))
        p.translate(self.width() / 2, self.height() / 2 - 8)
        p.scale(s, s)
        r = QRectF(-w / 2, -h / 2, w, h)
        path = QPainterPath()
        path.addRoundedRect(r, 14, 14)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setClipPath(path)
        p.drawPixmap(r.topLeft(), scaled)
        p.restore()
        p.setPen(QColor(255, 255, 255, int(200 * self.pp)))
        p.setFont(font(13, W_MED))
        p.drawText(QRectF(0, self.height() - 64, self.width(), 30), A_CENTER,
                   (self.caption + "     " if self.caption else "") + "Click anywhere to close")


def QSizeF_fit(w, h):
    return (max(100, w), max(100, h))


# ════════════════════════════════════════════════════════════════════════════
#  Toast
# ════════════════════════════════════════════════════════════════════════════
class Toast(Animated, QWidget):
    def __init__(self, win, text: str, kind: str = "ok", action_text: str = "", action=None):
        super().__init__(win)
        self.kind, self.text_, self.action_text, self.action = kind, text, action_text, action
        self.setFont(font(14, W_MED))
        fm = QFontMetrics(self.font())
        self.tw = min(fm.horizontalAdvance(text), max(120, win.width() - 260))
        self.aw = fm.horizontalAdvance(action_text) if action_text else 0
        w = 22 + 22 + 12 + self.tw + ((28 + self.aw) if action_text else 0) + 24
        self.resize(int(w), 52)
        self.setCursor(Qt.CursorShape.PointingHandCursor if action else Qt.CursorShape.ArrowCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, action is None)

    def _action_rect(self) -> QRectF:
        return QRectF(self.width() - 24 - self.aw - 8, 8, self.aw + 16, self.height() - 16)

    def mousePressEvent(self, e):
        if self.action and self._action_rect().contains(QPointF(e.position())):
            self.action()
            self.win_dismiss()

    def win_dismiss(self):
        w = self.parentWidget()
        if w is not None and hasattr(w, "drop_toast"):
            w.drop_toast(self)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(1, 1, -1, -1)
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(8, 0, -1):
            p.setBrush(QColor(8, 10, 18, 5))
            p.drawRoundedRect(r.adjusted(-i * 0.6, -i * 0.6 + 3, i * 0.6, i * 0.6 + 3), 26 + i, 26 + i)
        p.setBrush(C("ink"))
        p.drawRoundedRect(r, 26, 26)
        name, col = {"ok": ("check-circle", QColor("#34D399") if not Theme.dark() else QColor("#0F9D63")),
                     "error": ("alert", QColor("#FF8496") if not Theme.dark() else QColor("#D6304A")),
                     "info": ("info", QColor("#8FA7FF") if not Theme.dark() else QColor("#3055F5"))}[self.kind]
        p.drawPixmap(QPointF(20, (self.height() - 22) / 2), icon_pm(name, col, 22, self.devicePixelRatioF(), 2.0))
        p.setFont(self.font())
        p.setPen(C("on_ink"))
        fm = QFontMetrics(self.font())
        p.drawText(QRectF(54, 0, self.tw + 4, self.height()), A_LEFT,
                   fm.elidedText(self.text_, Qt.TextElideMode.ElideRight, self.tw))
        if self.action_text:
            p.setPen(QColor("#8FA7FF") if not Theme.dark() else QColor("#3055F5"))
            p.drawText(QRectF(self.width() - 24 - self.aw, 0, self.aw + 4, self.height()), A_LEFT, self.action_text)


# ════════════════════════════════════════════════════════════════════════════
#  Page host - quick cross-fade between screens
# ════════════════════════════════════════════════════════════════════════════
class PageHost(TWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.current: QWidget | None = None
        self.pages: list[QWidget] = []
        self._token = 0

    def add(self, page: QWidget):
        page.setParent(self)
        page.setGeometry(self.rect())
        page.hide()
        self.pages.append(page)

    def resizeEvent(self, e):
        for pg in self.pages:
            pg.setGeometry(self.rect())

    def show_page(self, page: QWidget, fade: bool = True, on_start=None):
        self._token += 1
        tok = self._token
        old, self.current = self.current, page
        for pg in self.pages:
            if pg is not page and pg is not old:
                pg.hide()
                _drop_fx(pg)

        def reveal():
            if tok != self._token:
                return
            if old is not None and old is not page:
                old.hide()
                _drop_fx(old)
            page.setGeometry(self.rect())
            page.show()
            page.raise_()
            if on_start:
                on_start()
            if fade:
                fade_in(page, 230)

        if old is None or old is page or not old.isVisible() or not Motion.on:
            reveal()
        else:
            fade_out(old, 110, reveal)


# ════════════════════════════════════════════════════════════════════════════
#  Responsive card grid (CSS-grid-like auto-fill, no fixed column count)
# ════════════════════════════════════════════════════════════════════════════
class FlowGrid(QWidget):
    def __init__(self, min_w: int = 296, max_w: int = 380, card_h: int = 210, gap: int = 16, parent=None):
        super().__init__(parent)
        self.min_w, self.max_w, self.card_h, self.gap = min_w, max_w, card_h, gap
        self.cards: list[QWidget] = []

    def columns(self, width: int | None = None) -> int:
        w = self.width() if width is None else width
        return max(1, int((w + self.gap) // (self.min_w + self.gap)))

    def set_cards(self, cards: list[QWidget], animate: bool = True):
        for c in self.cards:
            c.setParent(None)
            c.deleteLater()
        self.cards = cards
        for c in self.cards:
            c.setParent(self)
        self._reflow(animate)

    def resizeEvent(self, e):
        self._reflow(False)

    def _reflow(self, animate: bool):
        if not self.cards:
            self.setMinimumHeight(0)
            return
        cols = self.columns()
        card_w = min(self.max_w, (self.width() - (cols - 1) * self.gap) / max(1, cols))
        card_w = max(self.min_w * 0.9, card_w)
        for i, c in enumerate(self.cards):
            col, row = i % cols, i // cols
            x, y = round(col * (card_w + self.gap)), round(row * (self.card_h + self.gap))
            c.setGeometry(x, y, round(card_w), self.card_h)
            if animate:
                c.show()
                fade_in(c, 240, delay=min(i, 8) * 30, dy=10)
            else:
                c.show()
        rows = math.ceil(len(self.cards) / cols)
        self.setMinimumHeight(rows * self.card_h + (rows - 1) * self.gap)


# ════════════════════════════════════════════════════════════════════════════
#  Stat card
# ════════════════════════════════════════════════════════════════════════════
class StatCard(Panel):
    def __init__(self, icon: str, tone: str, title: str, fmt=inr, parent=None):
        super().__init__(20, "surface", True, parent)
        self.setFixedHeight(96)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(20, 18, 20, 18)
        lay.setSpacing(14)
        lay.addWidget(IconTile(icon, tone, 44))
        col = QVBoxLayout()
        col.setSpacing(4)
        col.addWidget(label(title, 12.5, W_MED, "text2"))
        self.value = AnimatedNumber(fmt, 21, W_SEMI)
        col.addWidget(self.value)
        self.sub = label("", 12, tone="text3")
        self.sub.hide()
        col.addWidget(self.sub)
        lay.addLayout(col, 1)

    def set_value(self, v, animate=True):
        self.value.set_value(v, animate)

    def set_sub(self, text: str):
        self.sub.setText(text)
        self.sub.setVisible(bool(text))


# ════════════════════════════════════════════════════════════════════════════
#  Renter card
# ════════════════════════════════════════════════════════════════════════════
class RenterCard(Animated, Panel):
    hv = fprop("hv")

    def __init__(self, win, d: dict, parent=None):
        super().__init__(22, "surface", True, parent)
        self.win, self.d = win, d
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setMouseTracking(True)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover)

        root = QVBoxLayout(self)
        root.setContentsMargins(18, 17, 16, 15)
        root.setSpacing(0)

        top = QHBoxLayout()
        top.setSpacing(12)
        self.avatar = AvatarView(52)
        top.addWidget(self.avatar)
        nm = QVBoxLayout()
        nm.setSpacing(3)
        self.name_l = label(d["name"], 15.5, W_SEMI, wrap=False)
        self.name_l.setFixedWidth(150)
        fm = QFontMetrics(self.name_l.font())
        self.name_l.setText(fm.elidedText(d["name"], Qt.TextElideMode.ElideRight, 150))
        self.name_l.setToolTip(d["name"])
        nm.addWidget(self.name_l)
        sub = f"ID {d['id']}" + (f"  ·  Room {d['room_no']}" if d.get("room_no") else "")
        nm.addWidget(label(sub, 12, tone="text3"))
        top.addLayout(nm, 1)
        self.status_pill = Pill("Active" if d["status"] == "active" else "Left",
                                 "green" if d["status"] == "active" else "slate")
        top.addWidget(self.status_pill, 0, Qt.AlignmentFlag.AlignTop)
        root.addLayout(top)
        root.addSpacing(13)

        if d.get("phone"):
            prow = QHBoxLayout()
            prow.setSpacing(7)
            prow.addWidget(Ico("phone", "text3", 13))
            prow.addWidget(label(d["phone"], 12.5, tone="text2"))
            prow.addStretch()
            root.addLayout(prow)
            root.addSpacing(9)
        else:
            root.addSpacing(9)

        badges = QHBoxLayout()
        badges.setSpacing(6)
        if d.get("pending_dues", 0) > 0:
            badges.addWidget(Pill(f"{inr(d['pending_dues'])} due", "amber", "alert-triangle", 11))
        if d.get("link_count", 0) > 0:
            badges.addWidget(Pill(f"{d['link_count']} linked", "slate", "link", 11))
        if d["status"] == "left":
            badges.addWidget(Pill(f"Left {pretty_date(d['left_date'])}", "slate", None, 11, outlined=True))
        badges.addStretch()
        root.addLayout(badges)
        root.addStretch(1)

        self.last_l = label(self._last_text(), 12, tone="text3", wrap=False)
        root.addWidget(self.last_l)
        root.addSpacing(11)

        bottom = QHBoxLayout()
        bottom.setSpacing(8)
        more = Btn("", "icon", "more", "sm")
        more.setFixedSize(34, 34)
        more.clicked.connect(self._open_menu)
        bottom.addWidget(more)
        bottom.addStretch()
        send = Btn("", "green", "arrow-right", "md")
        send.setFixedSize(42, 34)
        send.setToolTip("Send this month's rent")
        send.clicked.connect(lambda: win.open_send_rent(d["id"]))
        self._send_btn = send
        bottom.addWidget(send)
        root.addLayout(bottom)

        if d["status"] == "left":
            eff = QGraphicsOpacityEffect(self)
            eff.setOpacity(0.72)
            self.setGraphicsEffect(eff)

    def _last_text(self) -> str:
        d = self.d
        if not d.get("last_bill_at"):
            return "No bills sent yet"
        when = pretty_date(d["last_bill_at"])
        paid = "paid" if d.get("last_paid") else "unpaid"
        return f"Last bill {inr(d['last_total'])} · {when} · {paid}"

    def enterEvent(self, e):
        self._a("hv", 1.0, 150)

    def leaveEvent(self, e):
        self._a("hv", 0.0, 220)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.win.open_profile(self.d["id"])

    def _open_menu(self):
        rid, st = self.d["id"], self.d["status"]
        m = QMenu(self.win)
        act_view = m.addAction(QIcon(icon_pm("user", C("text"), 16)), "View profile")
        act_send = m.addAction(QIcon(icon_pm("send", C("text"), 16)), "Send rent")
        m.addSeparator()
        act_edit = m.addAction(QIcon(icon_pm("edit", C("text"), 16)), "Edit profile")
        act_status = m.addAction(QIcon(icon_pm("log-out" if st == "active" else "rotate", C("text"), 16)),
                                  "Mark as left" if st == "active" else "Mark as active")
        act_export = m.addAction(QIcon(icon_pm("download", C("text"), 16)), "Export this renter's data")
        m.addSeparator()
        act_delete = m.addAction(QIcon(icon_pm("trash", C("red_t"), 16)), "Delete renter")
        chosen = m.exec(QCursor.pos())
        if chosen == act_view:
            self.win.open_profile(rid)
        elif chosen == act_send:
            self.win.open_send_rent(rid)
        elif chosen == act_edit:
            self.win.open_edit_renter(rid)
        elif chosen == act_status:
            self.win.quick_toggle_status(rid)
        elif chosen == act_export:
            self.win.open_export([rid])
        elif chosen == act_delete:
            self.win.confirm_delete_renter(rid)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        lift = self.hv * 3
        shadow = QColor(8, 10, 18, int(26 * self.hv))
        if self.hv > 0.01:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(shadow)
            p.drawRoundedRect(r.translated(0, 3 + lift * 0.5).adjusted(2, 0, -2, 0), self.radius, self.radius)
        p.setBrush(mix(C("surface"), C("surface2"), self.hv * 0.5))
        p.setPen(QPen(mix(C("line"), C("line2"), self.hv), 1))
        p.drawRoundedRect(r.translated(0, -lift * 0.4), self.radius, self.radius)
        self.avatar.set_renter(self.d, dim=(self.d["status"] == "left"))


# ════════════════════════════════════════════════════════════════════════════
#  Empty state
# ════════════════════════════════════════════════════════════════════════════
class EmptyState(TWidget):
    def __init__(self, icon: str, title: str, body: str, cta_text: str = "", cta_icon: str = "plus",
                 on_cta=None, parent=None):
        super().__init__(parent)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(40, 64, 40, 64)
        lay.setSpacing(0)
        lay.setAlignment(Qt.AlignmentFlag.AlignHCenter)
        tile = IconTile(icon, "blue", 64)
        lay.addWidget(tile, 0, Qt.AlignmentFlag.AlignHCenter)
        lay.addSpacing(22)
        t = label(title, 19, W_SEMI, display=True, align=A_CENTER)
        lay.addWidget(t)
        lay.addSpacing(8)
        b = label(body, 14, tone="text2", align=A_CENTER, wrap=True)
        b.setFixedWidth(360)
        lay.addWidget(b, 0, Qt.AlignmentFlag.AlignHCenter)
        if cta_text:
            lay.addSpacing(24)
            btn = Btn(cta_text, "ink", cta_icon, "lg")
            if on_cta:
                btn.clicked.connect(on_cta)
            lay.addWidget(btn, 0, Qt.AlignmentFlag.AlignHCenter)


# ════════════════════════════════════════════════════════════════════════════
#  Home page - stats + search/filter + renter grid
# ════════════════════════════════════════════════════════════════════════════
class HomePage(TWidget):
    def __init__(self, win, parent=None):
        super().__init__(parent)
        self.win = win
        self.query = ""
        self.filter_idx = 0   # 0 all, 1 active, 2 left

        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        outer.addWidget(self.scroll)

        body = TWidget()
        self.scroll.setWidget(body)
        v = QVBoxLayout(body)
        v.setContentsMargins(36, 28, 36, 44)
        v.setSpacing(0)

        head = QHBoxLayout()
        title_col = QVBoxLayout()
        title_col.setSpacing(4)
        title_col.addWidget(label("Renters", 25, W_SEMI, display=True))
        self.subtitle = label("", 14, tone="text2")
        title_col.addWidget(self.subtitle)
        head.addLayout(title_col)
        head.addStretch()
        fetch = Btn("Fetch data", "soft", "download", "md")
        fetch.setToolTip("Download everyone's data as a zip file")
        fetch.clicked.connect(lambda: win.open_export(None))
        head.addWidget(fetch)
        head.addSpacing(10)
        add = Btn("Add renter", "ink", "plus", "md")
        add.clicked.connect(win.open_add_renter)
        head.addWidget(add)
        v.addLayout(head)
        v.addSpacing(22)

        stats = QHBoxLayout()
        stats.setSpacing(14)
        self.stat_active = StatCard("users", "blue", "Active renters", lambda x: str(int(x)))
        self.stat_billed = StatCard("rupee", "green", "Billed this month")
        self.stat_collected = StatCard("check-circle", "green", "Collected this month")
        self.stat_dues = StatCard("alert-triangle", "amber", "Pending dues")
        for s in (self.stat_active, self.stat_billed, self.stat_collected, self.stat_dues):
            stats.addWidget(s, 1)
        v.addLayout(stats)
        v.addSpacing(26)

        tools = QHBoxLayout()
        tools.setSpacing(12)
        self.search = Field("Search by name, phone, room or ID", "search")
        self.search.setFixedWidth(340)
        self.search.changed.connect(self._on_search)
        tools.addWidget(self.search)
        self.seg = Segmented(["All", "Active", "Left"])
        self.seg.changed.connect(self._on_filter)
        tools.addWidget(self.seg)
        tools.addStretch()
        v.addLayout(tools)
        v.addSpacing(20)

        self.stack_empty = EmptyState("user-plus", "No renters yet",
                                       "Add your first renter to start tracking rent, dues and documents "
                                       "all in one place.", "Add your first renter", "plus", win.open_add_renter)
        self.stack_none = EmptyState("search", "No matches", "Try a different name, phone number, room or ID.")
        self.grid = FlowGrid()
        v.addWidget(self.stack_empty)
        v.addWidget(self.stack_none)
        v.addWidget(self.grid)
        v.addStretch(1)
        self._all: list[dict] = []

    def _on_search(self, text: str):
        self.query = text.strip().lower()
        self.render()

    def _on_filter(self, idx: int):
        self.filter_idx = idx
        self.render()

    def _match(self, d: dict) -> bool:
        if self.filter_idx == 1 and d["status"] != "active":
            return False
        if self.filter_idx == 2 and d["status"] != "left":
            return False
        if not self.query:
            return True
        hay = " ".join(str(d.get(k, "")) for k in ("name", "phone", "alt_phone", "room_no", "id")).lower()
        return self.query in hay

    def load(self, animate: bool = True):
        self._all = self.win.db.list_renters()
        st = self.win.db.stats()
        n_total = len(self._all)
        self.subtitle.setText("Manage everyone renting from you" if n_total else
                               "Manage everyone renting from you — nobody added yet")
        self.stat_active.set_value(st["active"])
        self.stat_active.set_sub(f"{st['left']} left" if st["left"] else "")
        self.stat_billed.set_value(st["billed"])
        self.stat_billed.set_sub(f"{st['billed_n']} bill{'s' if st['billed_n'] != 1 else ''} this month")
        self.stat_collected.set_value(st["collected"])
        pct = (st["collected"] / st["billed"] * 100) if st["billed"] else None
        self.stat_collected.set_sub(f"{pct:.0f}% of billed" if pct is not None else "")
        self.stat_dues.set_value(st["dues"])
        self.stat_dues.set_sub(f"{st['dues_n']} renter{'s' if st['dues_n'] != 1 else ''}" if st["dues_n"] else "All clear")
        self.render(animate)

    def render(self, animate: bool = True):
        if not self._all:
            self.stack_empty.show()
            self.stack_none.hide()
            self.grid.hide()
            return
        self.stack_empty.hide()
        shown = [d for d in self._all if self._match(d)]
        if not shown:
            self.stack_none.show()
            self.grid.hide()
            return
        self.stack_none.hide()
        self.grid.show()
        self.grid.set_cards([RenterCard(self.win, d) for d in shown], animate)


# ════════════════════════════════════════════════════════════════════════════
#  Add / Edit renter - side drawer
# ════════════════════════════════════════════════════════════════════════════
class LinkRow(TWidget):
    removed = pyqtSignal()

    def __init__(self, other_id: int, name: str, status: str, relation: str, parent=None):
        super().__init__(parent)
        self.other_id = other_id
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(10)
        av = AvatarView(34)
        av.set_renter(dict(id=other_id, name=name), dim=(status == "left"))
        lay.addWidget(av)
        col = QVBoxLayout()
        col.setSpacing(1)
        nm = label(name, 13.5, W_SEMI)
        col.addWidget(nm)
        col.addWidget(label(f"ID {other_id}", 11.5, tone="text3"))
        lay.addLayout(col, 1)
        self.sel = Select(RELATIONS, relation if relation in RELATIONS else "Other")
        self.sel.setFixedWidth(128)
        lay.addWidget(self.sel)
        rm = Btn("", "icon", "x", "sm")
        rm.setFixedSize(30, 30)
        rm.setToolTip("Remove link")
        rm.clicked.connect(self.removed.emit)
        lay.addWidget(rm)

    def relation(self) -> str:
        return self.sel.value()


class RenterFormDrawer(Drawer):
    saved = pyqtSignal(int)

    def __init__(self, win, renter_id: int | None = None):
        super().__init__(win, 560)
        self.win = win
        self.editing = renter_id is not None
        self.rid = renter_id if self.editing else win.db.new_id()
        self.pending_links: dict[int, str] = {}
        if self.editing:
            for l in win.db.links_for(self.rid):
                self.pending_links[l["other_id"]] = l["relation"]

        root = QVBoxLayout(self.panel)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        head = QHBoxLayout()
        head.setContentsMargins(28, 24, 24, 18)
        title = "Edit renter" if self.editing else "Add renter"
        tcol = QVBoxLayout()
        tcol.setSpacing(3)
        tcol.addWidget(label(title, 20, W_SEMI, display=True))
        tcol.addWidget(label(f"ID {self.rid}  ·  permanent, can't be changed", 12, tone="text3"))
        head.addLayout(tcol, 1)
        close = Btn("", "icon", "x", "sm")
        close.setFixedSize(34, 34)
        close.clicked.connect(self.dismiss)
        head.addWidget(close, 0, Qt.AlignmentFlag.AlignTop)
        root.addLayout(head)
        root.addWidget(Divider())

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        root.addWidget(scroll, 1)
        body = TWidget()
        scroll.setWidget(body)
        v = QVBoxLayout(body)
        v.setContentsMargins(28, 22, 28, 22)
        v.setSpacing(22)

        # -- pictures --------------------------------------------------------
        pics = QHBoxLayout()
        pics.setSpacing(16)
        pcol = QVBoxLayout()
        pcol.setSpacing(8)
        pcol.addWidget(label("Profile picture", 13, W_MED, "text2"))
        self.photo_zone = DropZone("Add photo", "Click or drag", 112, 112, squircle=True, icon="camera")
        pcol.addWidget(self.photo_zone)
        pcol.addStretch()
        pics.addLayout(pcol)

        acol = QVBoxLayout()
        acol.setSpacing(8)
        arow_lbl = QHBoxLayout()
        arow_lbl.addWidget(label("Aadhaar card", 13, W_MED, "text2"))
        arow_lbl.addStretch()
        both_btn = Btn("Upload front + back, or a PDF", "link", size="sm")
        both_btn.clicked.connect(self._pick_aadhaar_files)
        arow_lbl.addWidget(both_btn)
        acol.addLayout(arow_lbl)
        azones = QHBoxLayout()
        azones.setSpacing(10)
        self.aadhaar_front_zone = DropZone("Front side", "Click, drag or drop a PDF", 154, 112,
                                            icon="id-card", accept_pdf=True)
        self.aadhaar_back_zone = DropZone("Back side", "Click, drag or drop a PDF", 154, 112,
                                           icon="id-card", accept_pdf=True)
        azones.addWidget(self.aadhaar_front_zone)
        azones.addWidget(self.aadhaar_back_zone)
        acol.addLayout(azones)
        self.aadhaar_hint_l = label("", 11.5, tone="text3", wrap=True)
        acol.addWidget(self.aadhaar_hint_l)
        pics.addLayout(acol, 1)
        v.addLayout(pics)

        for zone in (self.aadhaar_front_zone, self.aadhaar_back_zone):
            zone.pdf_chosen.connect(self._split_aadhaar_pdf)
            zone.changed.connect(self._schedule_aadhaar_ocr)
        self._ocr_timer = QTimer(self)
        self._ocr_timer.setSingleShot(True)
        self._ocr_timer.timeout.connect(self._run_aadhaar_ocr)
        self._ocr_thread: AadhaarOcrWorker | None = None

        # -- aadhaar details ---------------------------------------------------
        v.addWidget(self._section("Aadhaar details"))
        v.addWidget(label(
            "Filled in automatically from the photo/PDF where possible - check it over "
            "and fix anything that's missing or wrong." if OCR_AVAILABLE else
            "Auto-fill needs pytesseract, Pillow and Tesseract installed (see the top of "
            "this file) - for now, add the details below by hand.",
            12, tone="text3", wrap=True))
        arow0 = QHBoxLayout()
        arow0.setSpacing(14)
        self.aadhaar_number_f = Field("XXXX XXXX XXXX", "id-card", kind="aadhaar")
        arow0.addWidget(labeled("Aadhaar number", self.aadhaar_number_f), 1)
        self.aadhaar_name_f = Field("As printed on the card")
        arow0.addWidget(labeled("Name on card", self.aadhaar_name_f), 1)
        v.addLayout(arow0)
        arow0b = QHBoxLayout()
        arow0b.setSpacing(14)
        self.aadhaar_dob_f = Field("DD/MM/YYYY")
        arow0b.addWidget(labeled("DOB on card", self.aadhaar_dob_f), 1)
        self.aadhaar_gender_sel = Select(GENDERS, GENDERS[0])
        arow0b.addWidget(labeled("Gender on card", self.aadhaar_gender_sel), 1)
        v.addLayout(arow0b)
        self.aadhaar_father_f = Field("Father's / husband's / guardian's name")
        v.addWidget(labeled("Father's / guardian's name (on card)", self.aadhaar_father_f))
        self.aadhaar_address_f = Field("Address printed on the card", multiline=True)
        v.addWidget(labeled("Address on card", self.aadhaar_address_f))

        # -- identity ---------------------------------------------------------
        v.addWidget(self._section("Identity"))
        self.name_f = Field("Full name", "user")
        v.addWidget(labeled("Name", self.name_f))
        row1 = QHBoxLayout()
        row1.setSpacing(14)
        self.room_f = Field("e.g. 12", "home")
        row1.addWidget(labeled("Room number", self.room_f), 1)
        self.join_f = DateField()
        row1.addWidget(labeled("Joined on", self.join_f), 1)
        v.addLayout(row1)

        # -- contact ------------------------------------------------------------
        v.addWidget(self._section("Contact"))
        row2 = QHBoxLayout()
        row2.setSpacing(14)
        self.phone_f = Field("10-digit number", "phone", kind="phone")
        row2.addWidget(labeled("Phone", self.phone_f), 1)
        self.alt_phone_f = Field("Optional", "phone", kind="phone")
        row2.addWidget(labeled("Alternate phone", self.alt_phone_f), 1)
        v.addLayout(row2)
        row3 = QHBoxLayout()
        row3.setSpacing(14)
        self.father_f = Field("Optional")
        row3.addWidget(labeled("Father's name", self.father_f), 1)
        self.mother_f = Field("Optional")
        row3.addWidget(labeled("Mother's name", self.mother_f), 1)
        v.addLayout(row3)
        self.parent_phone_f = Field("Optional", "phone", kind="phone")
        v.addWidget(labeled("Parent / guardian phone", self.parent_phone_f))

        # -- billing defaults ------------------------------------------------------
        sec = self._section("Billing defaults")
        hint = label("Used to pre-fill the send-rent form - each bill can still change them", 12, tone="text3", wrap=True)
        secwrap = TWidget()
        scv = QVBoxLayout(secwrap)
        scv.setContentsMargins(0, 0, 0, 0)
        scv.setSpacing(4)
        scv.addWidget(sec)
        scv.addWidget(hint)
        v.addWidget(secwrap)
        row4 = QHBoxLayout()
        row4.setSpacing(14)
        self.rent_f = Field("0", prefix="₹", kind="money")
        row4.addWidget(labeled("Monthly rent", self.rent_f), 1)
        self.wifi_f = Field("0", prefix="₹", kind="money")
        row4.addWidget(labeled("WiFi fee", self.wifi_f), 1)
        self.rate_f = Field("0", prefix="₹", kind="money")
        row4.addWidget(labeled("One unit charge", self.rate_f), 1)
        v.addLayout(row4)

        # -- links ------------------------------------------------------------------
        v.addWidget(self._section("Linked renters"))
        v.addWidget(label("Roommate, sibling or anyone else this renter is connected to", 12, tone="text3", wrap=True))
        addrow = QHBoxLayout()
        addrow.setSpacing(10)
        self.link_id_f = Field("4-digit ID", "hash", kind="id")
        self.link_id_f.setFixedWidth(130)
        self.link_id_f.submitted.connect(self._add_link)
        addrow.addWidget(self.link_id_f)
        self.link_rel_sel = Select(RELATIONS, "Roommate")
        self.link_rel_sel.setFixedWidth(150)
        addrow.addWidget(self.link_rel_sel)
        addrow.addStretch()
        add_link_btn = Btn("Link", "soft", "link", "sm")
        add_link_btn.clicked.connect(self._add_link)
        addrow.addWidget(add_link_btn)
        v.addLayout(addrow)
        self.links_box = TWidget()
        self.links_lay = QVBoxLayout(self.links_box)
        self.links_lay.setContentsMargins(0, 4, 0, 0)
        self.links_lay.setSpacing(10)
        v.addWidget(self.links_box)
        self.no_links_l = label("No linked renters yet", 12.5, tone="text3")
        v.addWidget(self.no_links_l)

        # -- notes --------------------------------------------------------------------
        v.addWidget(self._section("Notes"))
        self.notes_f = Field("Anything worth remembering about this renter\u2026", multiline=True)
        v.addWidget(self.notes_f)
        v.addStretch(1)

        root.addWidget(Divider())
        foot = QHBoxLayout()
        foot.setContentsMargins(24, 16, 24, 16)
        foot.setSpacing(10)
        if self.editing:
            delete_btn = Btn("Delete", "danger", "trash", "md")
            delete_btn.clicked.connect(lambda: win.confirm_delete_renter(self.rid, after=self.dismiss))
            foot.addWidget(delete_btn)
        foot.addStretch()
        cancel = Btn("Cancel", "ghost", size="md")
        cancel.clicked.connect(self.dismiss)
        foot.addWidget(cancel)
        save = Btn("Save renter", "ink", "check", "md")
        save.clicked.connect(self._save)
        foot.addWidget(save)
        root.addLayout(foot)

        if self.editing:
            self._load_existing()
        else:
            self.join_f.set_iso(today_iso())
        self._refresh_links()

    def _section(self, text: str) -> QWidget:
        w = TWidget()
        lay = QHBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(10)
        lay.addWidget(label(text, 12, W_SEMI, "text3"))
        line = Divider()
        lay.addWidget(line, 1)
        return w

    def _load_existing(self):
        r = self.win.db.get_renter(self.rid)
        if not r:
            return
        self.name_f.setText(r["name"])
        self.room_f.setText(r["room_no"])
        self.join_f.set_iso(r["join_date"] or today_iso())
        self.phone_f.setText(r["phone"])
        self.alt_phone_f.setText(r["alt_phone"])
        self.father_f.setText(r["father_name"])
        self.mother_f.setText(r["mother_name"])
        self.parent_phone_f.setText(r["parent_phone"])
        self.rent_f.setText(num(r["monthly_rent"]))
        self.wifi_f.setText(num(r["wifi_fee"]))
        self.rate_f.setText(num(r["unit_rate"]))
        self.notes_f.setText(r["notes"])
        self.photo_zone.load(r["photo_path"])
        self.aadhaar_front_zone.load(r["aadhaar_front_path"])
        self.aadhaar_back_zone.load(r["aadhaar_back_path"])
        self.aadhaar_number_f.setText(r["aadhaar_number"])
        self.aadhaar_name_f.setText(r["aadhaar_name"])
        self.aadhaar_dob_f.setText(r["aadhaar_dob"])
        self.aadhaar_gender_sel.set_value(r["aadhaar_gender"] or GENDERS[0])
        self.aadhaar_father_f.setText(r["aadhaar_father"])
        self.aadhaar_address_f.setText(r["aadhaar_address"])

    # -- aadhaar upload: pdf splitting & auto-fill ------------------------------------
    def _pick_aadhaar_files(self):
        start = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.PicturesLocation)
        paths, _ = QFileDialog.getOpenFileNames(
            self.win, "Choose the Aadhaar card - front & back images, or one PDF", start, AADHAAR_FILTER)
        if not paths:
            return
        if len(paths) == 1 and is_pdf(paths[0]):
            self._split_aadhaar_pdf(paths[0])
            return
        images = [p for p in paths if is_image(p)]
        if not images:
            self.toast_local("Choose PNG/JPG images, or a single PDF of the Aadhaar card.")
            return
        self.aadhaar_front_zone.stage(images[0])
        if len(images) > 1:
            self.aadhaar_back_zone.stage(images[1])

    def _split_aadhaar_pdf(self, pdf_path: str):
        if not PDF_AVAILABLE:
            self.toast_local("Reading PDFs needs PyMuPDF installed (pip install PyMuPDF). "
                              "Upload the front and back as images instead, for now.")
            return
        pages = render_pdf_pages(pdf_path, max_pages=2)
        if not pages:
            self.toast_local("Couldn't read that PDF. Try uploading it as images instead.")
            return
        self.aadhaar_front_zone.stage(pages[0])
        if len(pages) > 1:
            self.aadhaar_back_zone.stage(pages[1])
        else:
            self.win.toast("Only one page found - fetched what we could from it. "
                            "Add the back separately if you have it, or fill in the rest by hand.", "info")

    def _schedule_aadhaar_ocr(self):
        self._ocr_timer.start(200)  # coalesce front+back landing in the same instant

    def _run_aadhaar_ocr(self):
        if not OCR_AVAILABLE:
            return
        paths = [p for p in (self.aadhaar_front_zone.current_path(), self.aadhaar_back_zone.current_path()) if p]
        if not paths or self._ocr_thread is not None:
            return
        self.aadhaar_hint_l.setText("Reading the card\u2026")
        self._ocr_thread = AadhaarOcrWorker(paths, self)
        self._ocr_thread.done.connect(self._apply_ocr_result)
        self._ocr_thread.failed.connect(self._ocr_failed)
        self._ocr_thread.finished.connect(self._ocr_cleanup)
        self._ocr_thread.start()

    def _ocr_cleanup(self):
        self._ocr_thread = None

    def _apply_ocr_result(self, data: dict):
        # Only fills in fields that are still blank - it never overwrites something
        # the person already typed, whether that came from an earlier scan or by hand.
        filled = []
        if data.get("number") and not self.aadhaar_number_f.text().strip():
            self.aadhaar_number_f.setText(data["number"])
            filled.append("Aadhaar number")
        if data.get("name") and not self.aadhaar_name_f.text().strip():
            self.aadhaar_name_f.setText(data["name"])
            filled.append("name")
        if data.get("dob") and not self.aadhaar_dob_f.text().strip():
            self.aadhaar_dob_f.setText(data["dob"])
            filled.append("DOB")
        if data.get("gender") and self.aadhaar_gender_sel.value() == GENDERS[0]:
            gender = data["gender"] if data["gender"] in GENDERS else "Other"
            self.aadhaar_gender_sel.set_value(gender)
            filled.append("gender")
        if data.get("father") and not self.aadhaar_father_f.text().strip():
            self.aadhaar_father_f.setText(data["father"])
            filled.append("father's/guardian's name")
        if data.get("address") and not self.aadhaar_address_f.text().strip():
            self.aadhaar_address_f.setText(data["address"])
            filled.append("address")
        if filled:
            self.aadhaar_hint_l.setText("Auto-filled " + ", ".join(filled) + " - please double-check them.")
        else:
            self.aadhaar_hint_l.setText("Couldn't make out the details from that photo - add them by hand below.")

    def _ocr_failed(self, msg: str):
        self.aadhaar_hint_l.setText("Couldn't scan that automatically - add the details by hand below.")

    # -- links ui ---------------------------------------------------------------------
    def _add_link(self):
        txt = self.link_id_f.text().strip()
        if len(txt) != 4 or not txt.isdigit():
            self.toast_local("Enter the renter's 4-digit ID.")
            shake(self.link_id_f)
            return
        other = int(txt)
        if other == self.rid:
            self.toast_local("A renter can't be linked to themselves.")
            shake(self.link_id_f)
            return
        other_r = self.win.db.get_renter(other)
        if not other_r:
            self.toast_local(f"No renter has ID {other}.")
            shake(self.link_id_f)
            return
        self.pending_links[other] = self.link_rel_sel.value()
        self.link_id_f.setText("")
        self._refresh_links()

    def toast_local(self, text: str):
        self.win.toast(text, "error")

    def _refresh_links(self):
        while self.links_lay.count():
            item = self.links_lay.takeAt(0)
            w = item.widget()
            if w:
                w.hide()
                w.setParent(None)
                w.deleteLater()
        ids = list(self.pending_links.keys())
        self.no_links_l.setVisible(not ids)
        for other in ids:
            r = self.win.db.get_renter(other)
            if not r:
                continue
            row = LinkRow(other, r["name"], r["status"], self.pending_links[other])

            def make_remover(oid=other):
                def _rm():
                    self.pending_links.pop(oid, None)
                    self._refresh_links()
                return _rm
            row.removed.connect(make_remover())
            self.links_lay.addWidget(row)

    # -- save -------------------------------------------------------------------------
    def _collect(self) -> dict:
        gender = self.aadhaar_gender_sel.value()
        return dict(
            name=self.name_f.text().strip(), phone=self.phone_f.text().strip(),
            alt_phone=self.alt_phone_f.text().strip(), father_name=self.father_f.text().strip(),
            mother_name=self.mother_f.text().strip(), parent_phone=self.parent_phone_f.text().strip(),
            room_no=self.room_f.text().strip(), join_date=self.join_f.iso(),
            notes=self.notes_f.text().strip(), monthly_rent=self.rent_f.value(),
            wifi_fee=self.wifi_f.value(), unit_rate=self.rate_f.value(),
            aadhaar_number=format_aadhaar_number(self.aadhaar_number_f.text()) or self.aadhaar_number_f.text().strip(),
            aadhaar_name=self.aadhaar_name_f.text().strip(), aadhaar_dob=self.aadhaar_dob_f.text().strip(),
            aadhaar_gender=gender if gender != GENDERS[0] else "",
            aadhaar_father=self.aadhaar_father_f.text().strip(), aadhaar_address=self.aadhaar_address_f.text().strip(),
        )

    def _save(self):
        if not self.name_f.text().strip():
            self.name_f.set_error(True)
            self.toast_local("This renter needs a name.")
            return
        self.name_f.set_error(False)
        d = self._collect()
        db = self.win.db
        for zone, folder, tag, key in ((self.photo_zone, PHOTO_DIR, "profile", "photo_path"),
                                        (self.aadhaar_front_zone, AADHAAR_DIR, "aadhaar_front", "aadhaar_front_path"),
                                        (self.aadhaar_back_zone, AADHAAR_DIR, "aadhaar_back", "aadhaar_back_path")):
            state, val = zone.state()
            if state == "new":
                old_rel = db.get_renter(self.rid)[key] if self.editing else ""
                remove_data_file(old_rel)
                d[key] = store_image(val, folder, self.rid, tag)
                self._forget_temp(val)
            elif state == "remove":
                old_rel = db.get_renter(self.rid)[key] if self.editing else ""
                remove_data_file(old_rel)
                d[key] = ""
            else:
                d[key] = db.get_renter(self.rid)[key] if self.editing else ""
        if self.editing:
            db.update_renter(self.rid, d)
        else:
            db.create_renter(self.rid, d)
        db.set_links(self.rid, self.pending_links)
        self.saved.emit(self.rid)
        self.win.toast(f"Saved {d['name'] or 'renter'}.", "ok")
        self.dismiss()

    def dismiss(self, *a):
        # Let a still-running OCR scan finish quietly rather than being torn down mid-flight.
        if getattr(self, "_ocr_thread", None) is not None:
            self._ocr_thread.quit()
            self._ocr_thread.wait(1000)
        for zone in (self.aadhaar_front_zone, self.aadhaar_back_zone):
            self._forget_temp(zone.staged)
        super().dismiss(*a)

    @staticmethod
    def _forget_temp(path: str):
        """Cleans up a PDF-page PNG rendered into .cache once it's no longer needed
        (either it's been copied into permanent storage, or the drawer is closing)."""
        try:
            if path and str(CACHE_DIR) in path and os.path.isfile(path):
                os.remove(path)
        except Exception:
            pass


# ════════════════════════════════════════════════════════════════════════════
#  Small profile-page building blocks
# ════════════════════════════════════════════════════════════════════════════
class AadhaarThumb(QWidget):
    """Small clickable preview of one side of an Aadhaar card. Shows a placeholder
    until a picture is loaded; only clickable (to open the full-size Viewer) once it has one."""
    clicked = pyqtSignal()

    def __init__(self, caption: str, w: int = 150, h: int = 96, parent=None):
        super().__init__(parent)
        self.caption = caption
        self.path = ""
        self.setFixedSize(w, h)

    def set_path(self, path: str):
        self.path = path or ""
        self.setCursor(Qt.CursorShape.PointingHandCursor if self.path else Qt.CursorShape.ArrowCursor)
        self.update()

    def has_image(self) -> bool:
        return bool(self.path) and os.path.isfile(self.path)

    def mousePressEvent(self, e):
        if self.has_image() and e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.SmoothPixmapTransform)
        R = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        dpr = self.devicePixelRatioF()
        if self.has_image():
            pm = cover_pixmap(self.path, int(R.width()), int(R.height()), 14, dpr)
            if pm is not None:
                p.drawPixmap(R.topLeft(), pm)
            p.setPen(QPen(C("line"), 1))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(R, 14, 14)
            p.setPen(QColor(255, 255, 255, 235))
            p.setFont(font(11, W_SEMI))
            p.setBrush(QColor(8, 10, 18, 120))
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRoundedRect(QRectF(R.left() + 6, R.bottom() - 24, 60, 18), 9, 9)
            p.setPen(QColor(255, 255, 255, 235))
            p.drawText(QRectF(R.left() + 6, R.bottom() - 24, 60, 18), A_CENTER, self.caption)
        else:
            p.setPen(QPen(C("line2"), 1.4))
            p.setBrush(C("surface2"))
            p.drawRoundedRect(R, 14, 14)
            p.drawPixmap(QPointF(R.center().x() - 11, R.center().y() - 20),
                         icon_pm("id-card", C("text3"), 22, dpr, 2.0))
            p.setFont(font(12, W_MED))
            p.setPen(C("text3"))
            p.drawText(QRectF(R.left(), R.center().y() + 2, R.width(), 20), A_CENTER, self.caption)
            p.setFont(font(10.5))
            p.drawText(QRectF(R.left(), R.center().y() + 20, R.width(), 16), A_CENTER, "Not on file")


class InfoRow(TWidget):
    def __init__(self, icon: str, label_text: str, value: str, parent=None):
        super().__init__(parent)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        tile = IconTile(icon, "ink", 36)
        lay.addWidget(tile)
        col = QVBoxLayout()
        col.setSpacing(1)
        col.addWidget(label(label_text, 11.5, tone="text3"))
        vl = label(value or "\u2014", 14, W_MED, wrap=True)
        col.addWidget(vl)
        lay.addLayout(col, 1)
        self.value_label = vl


class SectionCard(Panel):
    def __init__(self, title: str, icon: str = "", trailing: QWidget | None = None, parent=None):
        super().__init__(22, "surface", True, parent)
        self.v = QVBoxLayout(self)
        self.v.setContentsMargins(22, 20, 22, 20)
        self.v.setSpacing(14)
        head = QHBoxLayout()
        head.setSpacing(10)
        if icon:
            ic = Ico(icon, "text3", 16, 2.1)
            head.addWidget(ic)
        head.addWidget(label(title, 14.5, W_SEMI))
        head.addStretch()
        if trailing:
            head.addWidget(trailing)
        self.v.addLayout(head)

    def body(self, w: QWidget):
        self.v.addWidget(w)


class DueRow(TWidget):
    changed = pyqtSignal()

    def __init__(self, win, due: dict, parent=None):
        super().__init__(parent)
        self.win, self.due = win, due
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        cleared = due["status"] == "cleared"
        dot = Pill("Cleared" if cleared else "Pending", "slate" if cleared else "amber", None, 10.5)
        dot.setFixedWidth(dot.sizeHint().width())
        lay.addWidget(dot)
        col = QVBoxLayout()
        col.setSpacing(1)
        rl = label(due["reason"] or "Overdue", 13.5, W_MED)
        if cleared:
            f = rl.font()
            col.addWidget(rl)
        else:
            col.addWidget(rl)
        sub = pretty_date(due["due_date"]) if due["due_date"] else pretty_date(due["created_at"])
        col.addWidget(label(sub, 11.5, tone="text3"))
        lay.addLayout(col, 1)
        lay.addWidget(label(inr(due["amount"]), 14, W_SEMI, "amber" if not cleared else "text3"))
        toggle = Btn("", "icon", "check" if not cleared else "rotate", "sm")
        toggle.setFixedSize(30, 30)
        toggle.setToolTip("Mark cleared" if not cleared else "Reopen")
        toggle.clicked.connect(self._toggle)
        lay.addWidget(toggle)
        rm = Btn("", "icon", "trash", "sm")
        rm.setFixedSize(30, 30)
        rm.clicked.connect(self._delete)
        lay.addWidget(rm)

    def _toggle(self):
        self.win.db.set_due_status(self.due["id"], "pending" if self.due["status"] == "cleared" else "cleared")
        self.changed.emit()

    def _delete(self):
        self.win.db.delete_due(self.due["id"])
        self.changed.emit()


class BillRow(TWidget):
    changed = pyqtSignal()

    def __init__(self, win, bill: dict, parent=None):
        super().__init__(parent)
        self.win, self.bill = win, bill
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        tile = IconTile("rupee", "green" if bill["paid"] else "amber", 36)
        lay.addWidget(tile)
        col = QVBoxLayout()
        col.setSpacing(1)
        col.addWidget(label(inr(bill["subtotal"]), 14, W_SEMI))
        meter = f"{num(bill['primary_unit'])}\u2192{num(bill['main_unit'])} units" if bill["has_reading"] else "No meter reading"
        col.addWidget(label(f"{pretty_dt(bill['created_at'])}  ·  {meter}", 11.5, tone="text3"))
        lay.addLayout(col, 1)
        paid_btn = Btn("Paid" if bill["paid"] else "Mark paid", "soft" if not bill["paid"] else "ghost", "check" if bill["paid"] else None, "sm")
        paid_btn.clicked.connect(self._toggle_paid)
        lay.addWidget(paid_btn)

    def _toggle_paid(self):
        self.win.db.set_bill_paid(self.bill["id"], not self.bill["paid"])
        self.changed.emit()


class LinkChip(Animated, TWidget):
    hv = fprop("hv")

    def __init__(self, win, link: dict, parent=None):
        super().__init__(parent)
        self.win, self.link = win, link
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFixedHeight(60)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(10, 8, 12, 8)
        lay.setSpacing(12)
        av = AvatarView(38)
        av.set_renter(dict(id=link["other_id"], name=link["name"], photo_path=link["photo_path"]),
                      dim=(link["status"] == "left"))
        lay.addWidget(av)
        col = QVBoxLayout()
        col.setSpacing(1)
        col.addWidget(label(link["name"], 13.5, W_SEMI))
        sub = f"ID {link['other_id']}" + (f"  ·  Room {link['room_no']}" if link.get("room_no") else "")
        col.addWidget(label(sub, 11.5, tone="text3"))
        lay.addLayout(col, 1)
        lay.addWidget(Pill(link["relation"], "slate", None, 11))
        lay.addWidget(Ico("chevron-right", "text3", 15))

    def enterEvent(self, e):
        self._a("hv", 1.0, 140)

    def leaveEvent(self, e):
        self._a("hv", 0.0, 200)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.win.open_profile(self.link["other_id"])

    def paintEvent(self, e):
        if self.hv > 0.01:
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(C("surface2", self.hv))
            p.drawRoundedRect(QRectF(self.rect()), 14, 14)
        super().paintEvent(e)


# ════════════════════════════════════════════════════════════════════════════
#  Profile page
# ════════════════════════════════════════════════════════════════════════════
class ProfilePage(TWidget):
    def __init__(self, win, parent=None):
        super().__init__(parent)
        self.win = win
        self.rid: int | None = None
        self.history: list[int] = []

        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        outer.addWidget(self.scroll)

        body = TWidget()
        self.scroll.setWidget(body)
        self.col = QVBoxLayout(body)
        self.col.setContentsMargins(36, 24, 36, 44)
        self.col.setSpacing(18)

        # -- header ----------------------------------------------------------------
        topbar = QHBoxLayout()
        back = Btn("Back", "ghost", "arrow-left", "sm")
        back.clicked.connect(self.go_back)
        topbar.addWidget(back)
        topbar.addStretch()
        self.col.addLayout(topbar)

        head = Panel(24, "surface", True)
        hl = QHBoxLayout(head)
        hl.setContentsMargins(24, 22, 24, 22)
        hl.setSpacing(18)
        self.avatar = AvatarView(76, clickable=True)
        self.avatar.clicked.connect(self._view_photo)
        hl.addWidget(self.avatar)
        hcol = QVBoxLayout()
        hcol.setSpacing(6)
        nmrow = QHBoxLayout()
        nmrow.setSpacing(10)
        self.name_l = label("", 21, W_SEMI, display=True)
        nmrow.addWidget(self.name_l)
        self.status_pill = Pill("Active", "green")
        nmrow.addWidget(self.status_pill, 0, Qt.AlignmentFlag.AlignVCenter)
        nmrow.addStretch()
        hcol.addLayout(nmrow)
        self.sub_l = label("", 13, tone="text3")
        hcol.addWidget(self.sub_l)
        self.left_note_l = label("", 12.5, tone="amber", wrap=True)
        self.left_note_l.hide()
        hcol.addWidget(self.left_note_l)
        hl.addLayout(hcol, 1)

        actions = QVBoxLayout()
        actions.setSpacing(8)
        send_btn = Btn("Send rent", "green", "send", "md")
        send_btn.clicked.connect(lambda: win.open_send_rent(self.rid))
        actions.addWidget(send_btn)
        arow = QHBoxLayout()
        arow.setSpacing(8)
        edit_btn = Btn("Edit", "soft", "edit", "sm")
        edit_btn.clicked.connect(lambda: win.open_edit_renter(self.rid))
        arow.addWidget(edit_btn)
        more_btn = Btn("", "icon", "more", "sm")
        more_btn.setFixedSize(34, 34)
        more_btn.clicked.connect(self._open_menu)
        arow.addWidget(more_btn)
        actions.addLayout(arow)
        hl.addLayout(actions)
        self.col.addWidget(head)

        # -- quick stats -------------------------------------------------------------
        stats = QHBoxLayout()
        stats.setSpacing(14)
        self.stat_dues = StatCard("alert-triangle", "amber", "Pending dues")
        self.stat_last = StatCard("rupee", "green", "Last bill")
        self.stat_room = StatCard("home", "blue", "Room", lambda x: str(x) if x else "\u2014")
        for s in (self.stat_dues, self.stat_last, self.stat_room):
            stats.addWidget(s, 1)
        self.col.addLayout(stats)

        # -- contact --------------------------------------------------------------------
        self.contact_card = SectionCard("Contact", "phone")
        self.contact_grid = QGridLayout()
        self.contact_grid.setHorizontalSpacing(20)
        self.contact_grid.setVerticalSpacing(16)
        cw = TWidget()
        cw.setLayout(self.contact_grid)
        self.contact_card.body(cw)
        self.col.addWidget(self.contact_card)

        # -- aadhaar card -----------------------------------------------------------------
        self.aadhaar_card = SectionCard("Aadhaar card", "id-card")
        acard_w = TWidget()
        acard_v = QVBoxLayout(acard_w)
        acard_v.setContentsMargins(0, 0, 0, 0)
        acard_v.setSpacing(14)

        thumbs_row = QHBoxLayout()
        thumbs_row.setSpacing(12)
        self.aadhaar_front_thumb = AadhaarThumb("Front")
        self.aadhaar_back_thumb = AadhaarThumb("Back")
        self.aadhaar_front_thumb.clicked.connect(lambda: self._view_aadhaar(self.aadhaar_front_thumb, "Front"))
        self.aadhaar_back_thumb.clicked.connect(lambda: self._view_aadhaar(self.aadhaar_back_thumb, "Back"))
        thumbs_row.addWidget(self.aadhaar_front_thumb)
        thumbs_row.addWidget(self.aadhaar_back_thumb)
        thumbs_row.addStretch(1)
        acard_v.addLayout(thumbs_row)

        numrow = QHBoxLayout()
        numrow.setSpacing(12)
        numrow.addWidget(IconTile("id-card", "ink", 36))
        ncol = QVBoxLayout()
        ncol.setSpacing(1)
        ncol.addWidget(label("Aadhaar number", 11.5, tone="text3"))
        self.aadhaar_number_l = label("\u2014", 14, W_MED)
        ncol.addWidget(self.aadhaar_number_l)
        numrow.addLayout(ncol, 1)
        self.aadhaar_reveal_btn = Btn("Show", "ghost", "eye", "sm")
        self.aadhaar_reveal_btn.clicked.connect(self._toggle_aadhaar_number)
        numrow.addWidget(self.aadhaar_reveal_btn)
        acard_v.addLayout(numrow)

        self.aadhaar_grid = QGridLayout()
        self.aadhaar_grid.setHorizontalSpacing(20)
        self.aadhaar_grid.setVerticalSpacing(16)
        agw = TWidget()
        agw.setLayout(self.aadhaar_grid)
        acard_v.addWidget(agw)
        self.aadhaar_card.body(acard_w)
        self.aadhaar_body_w = acard_w

        self.aadhaar_empty_w = TWidget()
        ew = QVBoxLayout(self.aadhaar_empty_w)
        ew.setContentsMargins(0, 0, 0, 0)
        ew.setSpacing(10)
        ew.addWidget(label("No Aadhaar card on file for this renter yet.", 13, tone="text3"))
        add_aadhaar_btn = Btn("Add Aadhaar details", "soft", "plus", "sm")
        add_aadhaar_btn.clicked.connect(lambda: win.open_edit_renter(self.rid))
        ew.addWidget(add_aadhaar_btn, 0, Qt.AlignmentFlag.AlignLeft)
        self.aadhaar_card.body(self.aadhaar_empty_w)
        self.col.addWidget(self.aadhaar_card)
        self._aadhaar_number_shown = False
        self._aadhaar_number_full = ""

        # -- billing defaults --------------------------------------------------------------
        self.billing_card = SectionCard("Billing defaults", "rupee")
        self.billing_grid = QGridLayout()
        self.billing_grid.setHorizontalSpacing(20)
        self.billing_grid.setVerticalSpacing(16)
        bw = TWidget()
        bw.setLayout(self.billing_grid)
        self.billing_card.body(bw)
        self.col.addWidget(self.billing_card)

        # -- dues -----------------------------------------------------------------------------
        add_due_btn = Btn("Add due", "soft", "plus", "sm")
        add_due_btn.clicked.connect(self._open_add_due)
        self.dues_card = SectionCard("Dues", "alert-triangle", add_due_btn)
        self.dues_list = TWidget()
        self.dues_lay = QVBoxLayout(self.dues_list)
        self.dues_lay.setContentsMargins(0, 0, 0, 0)
        self.dues_lay.setSpacing(12)
        self.dues_card.body(self.dues_list)
        self.dues_empty = label("No dues on record.", 13, tone="text3")
        self.dues_card.body(self.dues_empty)
        self.col.addWidget(self.dues_card)

        # -- links --------------------------------------------------------------------------------
        self.links_card = SectionCard("Linked renters", "link")
        self.links_list = TWidget()
        self.links_lay = QVBoxLayout(self.links_list)
        self.links_lay.setContentsMargins(0, 0, 0, 0)
        self.links_lay.setSpacing(8)
        self.links_card.body(self.links_list)
        self.links_empty = label("No linked renters.", 13, tone="text3")
        self.links_card.body(self.links_empty)
        self.col.addWidget(self.links_card)

        # -- bill history -----------------------------------------------------------------------------
        self.bills_card = SectionCard("Bill history", "file-text")
        self.bills_list = TWidget()
        self.bills_lay = QVBoxLayout(self.bills_list)
        self.bills_lay.setContentsMargins(0, 0, 0, 0)
        self.bills_lay.setSpacing(12)
        self.bills_card.body(self.bills_list)
        self.bills_empty = label("No bills sent yet.", 13, tone="text3")
        self.bills_card.body(self.bills_empty)
        self.col.addWidget(self.bills_card)

        # -- notes ------------------------------------------------------------------------------------
        self.notes_card = SectionCard("Notes", "edit")
        self.notes_l = label("", 13.5, tone="text2", wrap=True)
        self.notes_card.body(self.notes_l)
        self.col.addWidget(self.notes_card)
        self.col.addStretch(1)

    # -- navigation --------------------------------------------------------------------------
    def go_back(self):
        if self.history:
            self.win.open_profile(self.history.pop(), _record=False)
        else:
            self.win.go_home()

    def open(self, rid: int, push: bool = True):
        if push and self.rid is not None and self.rid != rid:
            self.history.append(self.rid)
        self.rid = rid
        self.load()

    def _open_menu(self):
        r = self.win.db.get_renter(self.rid)
        if not r:
            return
        m = QMenu(self.win)
        act_status = m.addAction(QIcon(icon_pm("log-out" if r["status"] == "active" else "rotate", C("text"), 16)),
                                  "Mark as left" if r["status"] == "active" else "Mark as active")
        act_export = m.addAction(QIcon(icon_pm("download", C("text"), 16)), "Export this renter's data")
        m.addSeparator()
        act_delete = m.addAction(QIcon(icon_pm("trash", C("red_t"), 16)), "Delete renter")
        chosen = m.exec(QCursor.pos())
        if chosen == act_status:
            self.win.quick_toggle_status(self.rid)
        elif chosen == act_export:
            self.win.open_export([self.rid])
        elif chosen == act_delete:
            self.win.confirm_delete_renter(self.rid, after=self.go_back)

    def _open_add_due(self):
        self.win.open_add_due(self.rid)

    # -- render -----------------------------------------------------------------------------------
    def load(self):
        r = self.win.db.get_renter(self.rid)
        if not r:
            self.win.go_home()
            return
        self.avatar.set_renter(r, dim=(r["status"] == "left"))
        self.name_l.setText(r["name"])
        self.status_pill.tone = "green" if r["status"] == "active" else "slate"
        self.status_pill.set_text("Active" if r["status"] == "active" else "Left")
        sub = f"ID {r['id']}"
        if r["room_no"]:
            sub += f"  ·  Room {r['room_no']}"
        if r["join_date"]:
            sub += f"  ·  Joined {pretty_date(r['join_date'])}"
        self.sub_l.setText(sub)
        if r["status"] == "left":
            note = f"Left on {pretty_date(r['left_date'])}"
            if r["left_note"]:
                note += f"  ·  {r['left_note']}"
            self.left_note_l.setText(note)
            self.left_note_l.show()
        else:
            self.left_note_l.hide()

        pending = self.win.db.pending_total(self.rid)
        self.stat_dues.set_value(pending, animate=False)
        self.stat_dues.set_sub("All clear" if pending == 0 else "Tap Dues below")
        last = self.win.db.last_bill(self.rid)
        self.stat_last.set_value(last["subtotal"] if last else 0, animate=False)
        self.stat_last.set_sub(pretty_date(last["created_at"]) if last else "No bills yet")
        self.stat_room.value.setText(r["room_no"] or "\u2014")
        self.stat_room.set_sub("Room number")

        self._fill_grid(self.contact_grid, [
            ("phone", "Phone", r["phone"]), ("phone", "Alternate phone", r["alt_phone"]),
            ("user", "Father's name", r["father_name"]), ("user", "Mother's name", r["mother_name"]),
            ("phone", "Parent / guardian phone", r["parent_phone"]),
        ])
        self._fill_grid(self.billing_grid, [
            ("rupee", "Monthly rent", inr(r["monthly_rent"])), ("wifi", "WiFi fee", inr(r["wifi_fee"])),
            ("zap", "One unit charge", inr(r["unit_rate"])),
        ])

        self._load_aadhaar(r)

        dues = self.win.db.dues_for(self.rid)
        self._fill_list(self.dues_lay, self.dues_empty, dues, lambda d: self._due_row(d))
        links = self.win.db.links_for(self.rid)
        self._fill_list(self.links_lay, self.links_empty, links, lambda l: LinkChip(self.win, l))
        bills = self.win.db.bills_for(self.rid, limit=12)
        self._fill_list(self.bills_lay, self.bills_empty, bills, lambda b: self._bill_row(b))

        self.notes_l.setText(r["notes"].strip() or "No notes yet.")
        set_tone(self.notes_l, "text2" if r["notes"].strip() else "text3")
        self.scroll.verticalScrollBar().setValue(0)

    def _due_row(self, d):
        row = DueRow(self.win, d)
        row.changed.connect(self.load)
        return row

    def _bill_row(self, b):
        row = BillRow(self.win, b)
        row.changed.connect(self.load)
        return row

    # -- photo / aadhaar viewing --------------------------------------------------------------
    def _view_photo(self):
        r = self.win.db.get_renter(self.rid)
        if r and r["photo_path"]:
            Viewer(self.win, abs_data(r["photo_path"]), r["name"]).open()

    def _view_aadhaar(self, thumb: "AadhaarThumb", caption: str):
        if thumb.has_image():
            Viewer(self.win, thumb.path, f"Aadhaar - {caption}").open()

    def _toggle_aadhaar_number(self):
        self._aadhaar_number_shown = not self._aadhaar_number_shown
        self.aadhaar_reveal_btn.setText("Hide" if self._aadhaar_number_shown else "Show")
        self.aadhaar_number_l.setText(
            self._aadhaar_number_full if self._aadhaar_number_shown else mask_aadhaar_number(self._aadhaar_number_full))

    def _load_aadhaar(self, r: dict):
        front = abs_data(r["aadhaar_front_path"])
        back = abs_data(r["aadhaar_back_path"])
        self.aadhaar_front_thumb.set_path(front if os.path.isfile(front) else "")
        self.aadhaar_back_thumb.set_path(back if os.path.isfile(back) else "")

        has_anything = bool(
            r["aadhaar_number"] or r["aadhaar_name"] or r["aadhaar_dob"] or r["aadhaar_gender"]
            or r["aadhaar_father"] or r["aadhaar_address"]
            or self.aadhaar_front_thumb.has_image() or self.aadhaar_back_thumb.has_image())
        self.aadhaar_body_w.setVisible(has_anything)
        self.aadhaar_empty_w.setVisible(not has_anything)

        self._aadhaar_number_shown = False
        self._aadhaar_number_full = r["aadhaar_number"] or ""
        self.aadhaar_reveal_btn.setText("Show")
        self.aadhaar_reveal_btn.setVisible(bool(self._aadhaar_number_full))
        self.aadhaar_number_l.setText(mask_aadhaar_number(self._aadhaar_number_full) if self._aadhaar_number_full else "\u2014")

        self._fill_grid(self.aadhaar_grid, [
            ("user", "Name on card", r["aadhaar_name"]),
            ("calendar", "DOB on card", r["aadhaar_dob"]),
            ("user", "Gender on card", r["aadhaar_gender"]),
            ("users", "Father's / guardian's name", r["aadhaar_father"]),
            ("home", "Address on card", r["aadhaar_address"]),
        ])

    def _fill_grid(self, grid: QGridLayout, rows: list[tuple]):
        while grid.count():
            item = grid.takeAt(0)
            w = item.widget()
            if w:
                w.hide()
                w.setParent(None)
                w.deleteLater()
        for i, (icon, cap, val) in enumerate(rows):
            grid.addWidget(InfoRow(icon, cap, val), i // 2, i % 2)

    def _fill_list(self, lay: QVBoxLayout, empty_l: QLabel, items: list, factory):
        while lay.count():
            item = lay.takeAt(0)
            w = item.widget()
            if w:
                w.hide()
                w.setParent(None)
                w.deleteLater()
        empty_l.setVisible(not items)
        for it in items:
            lay.addWidget(factory(it))


# ════════════════════════════════════════════════════════════════════════════
#  Send rent - side drawer
# ════════════════════════════════════════════════════════════════════════════
class KVRow(TWidget):
    def __init__(self, k: str, v_widget_or_text, bold: bool = False, tone: str = "text", parent=None):
        super().__init__(parent)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(10)
        lay.addWidget(label(k, 13.5 if bold else 13, W_SEMI if bold else W_NORMAL, "text" if bold else "text2"))
        lay.addStretch()
        if isinstance(v_widget_or_text, QWidget):
            lay.addWidget(v_widget_or_text)
        else:
            lay.addWidget(label(v_widget_or_text, 14.5 if bold else 13.5, W_BOLD if bold else W_MED, tone))


class SendRentDrawer(Drawer):
    def __init__(self, win, renter_id: int):
        super().__init__(win, 480)
        self.win = win
        self.rid = renter_id
        r = win.db.get_renter(renter_id) or {}
        self.renter = r

        root = QVBoxLayout(self.panel)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        head = QHBoxLayout()
        head.setContentsMargins(26, 22, 22, 16)
        head.setSpacing(12)
        av = AvatarView(44)
        av.set_renter(r)
        head.addWidget(av)
        tcol = QVBoxLayout()
        tcol.setSpacing(2)
        tcol.addWidget(label("Send rent", 18, W_SEMI, display=True))
        tcol.addWidget(label(f"{r.get('name','')}  ·  ID {renter_id}", 12.5, tone="text3"))
        head.addLayout(tcol, 1)
        close = Btn("", "icon", "x", "sm")
        close.setFixedSize(32, 32)
        close.clicked.connect(self.dismiss)
        head.addWidget(close, 0, Qt.AlignmentFlag.AlignTop)
        root.addLayout(head)
        root.addWidget(Divider())

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        root.addWidget(scroll, 1)
        body = TWidget()
        scroll.setWidget(body)
        v = QVBoxLayout(body)
        v.setContentsMargins(26, 20, 26, 20)
        v.setSpacing(20)

        # -- meter reading ---------------------------------------------------------------
        v.addWidget(self._section("Electricity meter"))
        last_bill = win.db.last_bill(renter_id)
        default_primary = last_bill["main_unit"] if last_bill else 0.0
        row1 = QHBoxLayout()
        row1.setSpacing(14)
        self.primary_f = Field("0", kind="units")
        self.primary_f.setText(num(default_primary))
        row1.addWidget(labeled("Primary unit (previous)", self.primary_f), 1)
        self.main_f = Field("0", kind="units")
        row1.addWidget(labeled("Main unit (current)", self.main_f), 1)
        v.addLayout(row1)
        self.rate_f = Field("0", prefix="₹", kind="money")
        self.rate_f.setText(num(r.get("unit_rate", 0)))
        v.addWidget(labeled("One unit charge", self.rate_f))
        self.has_reading_chk = Check("This bill includes a meter reading")
        self.has_reading_chk.setChecked(True)
        self.has_reading_chk.toggled.connect(self._on_reading_toggle)
        v.addWidget(self.has_reading_chk)

        # -- amounts --------------------------------------------------------------------------
        v.addWidget(self._section("Amounts"))
        row2 = QHBoxLayout()
        row2.setSpacing(14)
        self.rent_f = Field("0", prefix="₹", kind="money")
        self.rent_f.setText(num(r.get("monthly_rent", 0)))
        row2.addWidget(labeled("Rent", self.rent_f), 1)
        self.wifi_f = Field("0", prefix="₹", kind="money")
        self.wifi_f.setText(num(r.get("wifi_fee", 0)))
        row2.addWidget(labeled("WiFi fee", self.wifi_f), 1)
        v.addLayout(row2)

        pending = win.db.pending_total(renter_id)
        self.back_dues_f = Field("0", prefix="₹", kind="money")
        self.back_dues_f.setText(num(pending))
        v.addWidget(labeled("Back dues", self.back_dues_f,
                             f"{inr(pending)} currently pending" if pending else ""))
        self.clear_dues_chk = Check("Mark pending dues as cleared once sent")
        self.clear_dues_chk.setChecked(pending > 0)
        self.clear_dues_chk.setVisible(pending > 0)
        v.addWidget(self.clear_dues_chk)

        self.advance_chk = Check("Advance paid")
        v.addWidget(self.advance_chk)
        self.advance_f = Field("0", prefix="₹", kind="money")
        adv_wrap = Collapsible(labeled("Advance amount", self.advance_f))
        v.addWidget(adv_wrap)
        self.advance_chk.toggled.connect(lambda on: adv_wrap.set_open(on))

        # -- note ------------------------------------------------------------------------------
        v.addWidget(self._section("Note"))
        self.note_chk = Check("Include a note in the message")
        v.addWidget(self.note_chk)
        self.note_f = Field("e.g. Please pay by the 5th\u2026", multiline=True)
        note_wrap = Collapsible(self.note_f)
        v.addWidget(note_wrap)
        self.note_chk.toggled.connect(lambda on: note_wrap.set_open(on))

        # -- live preview --------------------------------------------------------------------------
        v.addWidget(self._section("Summary"))
        self.preview_panel = Panel(16, "surface2", False)
        pv = QVBoxLayout(self.preview_panel)
        pv.setContentsMargins(16, 14, 16, 14)
        pv.setSpacing(9)
        self.row_units = KVRow("Units used", "0")
        pv.addWidget(self.row_units)
        self.row_elec = KVRow("Electricity", "\u20b90")
        pv.addWidget(self.row_elec)
        pv.addWidget(Divider())
        self.row_total = KVRow("Total", "\u20b90", bold=True, tone="text")
        pv.addWidget(self.row_total)
        v.addWidget(self.preview_panel)
        v.addStretch(1)

        for f in (self.primary_f, self.main_f, self.rate_f, self.rent_f, self.wifi_f,
                  self.back_dues_f, self.advance_f):
            f.changed.connect(self._recalc)

        root.addWidget(Divider())
        foot = QVBoxLayout()
        foot.setContentsMargins(24, 14, 24, 16)
        foot.setSpacing(10)
        self.total_l = AnimatedNumber(inr, 26, W_BOLD)
        totrow = QHBoxLayout()
        totrow.addWidget(label("Subtotal", 13, tone="text2"))
        totrow.addStretch()
        totrow.addWidget(self.total_l)
        foot.addLayout(totrow)
        btnrow = QHBoxLayout()
        btnrow.setSpacing(10)
        save_only = Btn("Save only", "ghost", size="md")
        save_only.clicked.connect(lambda: self._submit(send=False))
        btnrow.addWidget(save_only)
        btnrow.addStretch()
        send = Btn("Send via WhatsApp", "green", "send", "md")
        send.clicked.connect(lambda: self._submit(send=True))
        btnrow.addWidget(send)
        foot.addLayout(btnrow)
        root.addLayout(foot)

        self._on_reading_toggle(True)
        self._recalc()

    def _section(self, text: str) -> QWidget:
        w = TWidget()
        lay = QHBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(10)
        lay.addWidget(label(text, 12, W_SEMI, "text3"))
        lay.addWidget(Divider(), 1)
        return w

    def _on_reading_toggle(self, on: bool):
        for w in (self.primary_f, self.main_f, self.rate_f):
            w.setEnabled(on)
        self._recalc()

    def _bill_dict(self) -> dict:
        has_reading = self.has_reading_chk.isChecked()
        primary = self.primary_f.value() if has_reading else 0.0
        main = self.main_f.value() if has_reading else 0.0
        rate = self.rate_f.value() if has_reading else 0.0
        b = compute_bill(self.rent_f.value(), primary, main, rate, self.wifi_f.value(),
                          self.back_dues_f.value(), self.advance_f.value() if self.advance_chk.isChecked() else 0.0)
        b.update(dict(primary_unit=primary, main_unit=main, unit_rate=rate, rent=self.rent_f.value(),
                      wifi_fee=self.wifi_f.value(), back_dues=self.back_dues_f.value(),
                      advance=self.advance_f.value() if self.advance_chk.isChecked() else 0.0,
                      note=self.note_f.text(), include_note=self.note_chk.isChecked(), has_reading=has_reading))
        return b

    def _recalc(self, *_):
        b = self._bill_dict()
        self._set_kv(self.row_units, num(b["units"]) + " units" if b["has_reading"] else "\u2014")
        self._set_kv(self.row_elec, inr(b["electricity"]))
        self._set_kv(self.row_total, inr(b["subtotal"]))
        self.total_l.set_value(b["subtotal"], animate=False)

    def _set_kv(self, row: KVRow, text: str):
        labels = row.findChildren(QLabel)
        if labels:
            labels[-1].setText(text)

    def _submit(self, send: bool):
        if self.has_reading_chk.isChecked() and self.main_f.value() < self.primary_f.value():
            self.main_f.set_error(True)
            self.win.toast("Main unit should be at or above the primary unit.", "error")
            return
        self.main_f.set_error(False)
        b = self._bill_dict()
        when = datetime.now()
        msg = build_message(self.renter.get("name", ""), self.renter.get("phone", ""), when, b,
                             self.note_f.text(), self.note_chk.isChecked())
        self.win.db.add_bill(self.rid, b, msg, "whatsapp" if send else "manual")
        if self.clear_dues_chk.isChecked() and self.clear_dues_chk.isVisible():
            self.win.db.clear_all_pending(self.rid)
        self.win.db.update_defaults(self.rid, self.rent_f.value(), self.wifi_f.value(), self.rate_f.value())
        if send:
            wa = wa_number(self.renter.get("phone", ""))
            if wa:
                webbrowser.open("https://web.whatsapp.com/send?phone=" + wa + "&text=" + urllib.parse.quote(msg)
                                 + "&source=&data=&app_absent=")
                self.win.toast(f"Opening WhatsApp for {self.renter.get('name','')}.", "ok")
            else:
                self.win.toast("Saved. No phone number on file to open WhatsApp with.", "info")
        else:
            self.win.toast(f"Saved {inr(b['subtotal'])} bill for {self.renter.get('name','')}.", "ok")
        self.win.refresh_all()
        self.dismiss()


# ════════════════════════════════════════════════════════════════════════════
#  Export ("Fetch data") dialog
# ════════════════════════════════════════════════════════════════════════════
class ExportRow(TWidget):
    def __init__(self, d: dict, checked: bool, parent=None):
        super().__init__(parent)
        self.rid = d["id"]
        lay = QHBoxLayout(self)
        lay.setContentsMargins(4, 8, 4, 8)
        lay.setSpacing(12)
        self.chk = Check("")
        self.chk.setChecked(checked)
        self.chk.setFixedWidth(24)
        lay.addWidget(self.chk)
        av = AvatarView(36)
        av.set_renter(d, dim=(d["status"] == "left"))
        lay.addWidget(av)
        col = QVBoxLayout()
        col.setSpacing(1)
        col.addWidget(label(d["name"], 13.5, W_SEMI))
        sub = f"ID {d['id']}" + (f"  ·  Room {d['room_no']}" if d.get("room_no") else "")
        col.addWidget(label(sub, 11.5, tone="text3"))
        lay.addLayout(col, 1)
        has_photo = d.get("photo_path") and (DATA_DIR / d["photo_path"]).is_file()
        has_aadhaar = ((d.get("aadhaar_front_path") and (DATA_DIR / d["aadhaar_front_path"]).is_file())
                       or (d.get("aadhaar_back_path") and (DATA_DIR / d["aadhaar_back_path"]).is_file()))
        if has_photo:
            lay.addWidget(Ico("camera", "text3", 15))
        if has_aadhaar:
            lay.addWidget(Ico("id-card", "text3", 15))
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.chk.toggle()

    def is_checked(self) -> bool:
        return self.chk.isChecked()


class ExportDialog(Dialog):
    def __init__(self, win, rids: list[int] | None):
        all_renters = win.db.list_renters()
        preselect = set(rids) if rids else {d["id"] for d in all_renters}
        title = "Export this renter" if rids and len(rids) == 1 else "Export data"
        sub = ("Everything on file for this renter, packaged as a zip you can keep or send." if rids and len(rids) == 1
               else "Choose who to include. Each renter gets their own folder with a details file, "
                    "plus their photo and Aadhaar card if on file.")
        super().__init__(win, title, sub, 460)
        self.win = win
        self.rows: list[ExportRow] = []

        if len(all_renters) > 1:
            selrow = QHBoxLayout()
            self.all_chk = Check("Select all")
            self.all_chk.setChecked(len(preselect) == len(all_renters))
            self.all_chk.toggled.connect(self._toggle_all)
            selrow.addWidget(self.all_chk)
            selrow.addStretch()
            self.count_l = label("", 12.5, tone="text3")
            selrow.addWidget(self.count_l)
            self.body.addLayout(selrow)

        listw = TWidget()
        lv = QVBoxLayout(listw)
        lv.setContentsMargins(0, 4, 0, 4)
        lv.setSpacing(2)
        for d in all_renters:
            row = ExportRow(d, d["id"] in preselect)
            row.chk.toggled.connect(self._update_count)
            lv.addWidget(row)
            self.rows.append(row)
        if len(all_renters) > 6:
            scroll = QScrollArea()
            scroll.setWidgetResizable(True)
            scroll.setFrameShape(QFrame.Shape.NoFrame)
            scroll.setFixedHeight(300)
            scroll.setWidget(listw)
            self.body.addWidget(scroll)
        else:
            self.body.addWidget(listw)
        self._update_count()

        self.add_button("Cancel", "ghost")
        self.export_btn = self.add_button("Create zip", "ink", self._do_export, close=False, icon="download")

    def _toggle_all(self, on: bool):
        for r in self.rows:
            r.chk.setChecked(on)

    def _update_count(self, *_):
        n = sum(1 for r in self.rows if r.is_checked())
        if hasattr(self, "count_l"):
            self.count_l.setText(f"{n} selected")
        if hasattr(self, "all_chk"):
            self.all_chk.blockSignals(True)
            self.all_chk.setChecked(n == len(self.rows) and n > 0)
            self.all_chk.blockSignals(False)

    def _do_export(self):
        picked = [r.rid for r in self.rows if r.is_checked()]
        if not picked:
            self.win.toast("Pick at least one renter to export.", "error")
            return False
        default_name = "renters_export.zip" if len(picked) > 1 else safe_name(self.win.db.get_renter(picked[0])["name"]) + ".zip"
        docs = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.DocumentsLocation) or str(Path.home())
        dest, _ = QFileDialog.getSaveFileName(self.win, "Save export", str(Path(docs) / default_name), "Zip archive (*.zip)")
        if not dest:
            return False
        if not dest.lower().endswith(".zip"):
            dest += ".zip"
        try:
            n = export_zip(self.win.db, picked, dest)
        except Exception as ex:
            self.win.toast(f"Couldn't create the zip: {ex}", "error")
            return False
        self.win.toast(f"Exported {n} renter{'s' if n != 1 else ''} to {Path(dest).name}.", "ok",
                        action_text="Show in folder", action=lambda: reveal_in_folder(dest))
        return True


# ════════════════════════════════════════════════════════════════════════════
#  Add a due
# ════════════════════════════════════════════════════════════════════════════
class AddDueDialog(Dialog):
    def __init__(self, win, renter_id: int):
        super().__init__(win, "Add a due", "Record an overdue amount, a late fee, or anything else owed.", 420)
        self.win, self.rid = win, renter_id

        self.reason_sel = Select(DUE_REASONS, "Overdue rent")
        self.body.addWidget(labeled("Reason", self.reason_sel))
        self.other_f = Field("Describe the reason")
        other_wrap = Collapsible(labeled("Details", self.other_f))
        self.body.addWidget(other_wrap)
        self.reason_sel.changed.connect(lambda v: other_wrap.set_open(v == "Other"))

        row = QHBoxLayout()
        row.setSpacing(14)
        self.amount_f = Field("0", prefix="₹", kind="money", big=True)
        row.addWidget(labeled("Amount", self.amount_f), 1)
        self.date_f = DateField()
        self.date_f.set_iso(today_iso())
        row.addWidget(labeled("Due date", self.date_f), 1)
        w = TWidget()
        w.setLayout(row)
        self.body.addWidget(w)

        self.add_button("Cancel", "ghost")
        self.add_button("Add due", "ink", self._add, close=False, icon="plus")

    def _add(self):
        amount = self.amount_f.value()
        if amount <= 0:
            self.amount_f.set_error(True)
            self.win.toast("Enter an amount greater than zero.", "error")
            return False
        reason = self.other_f.text().strip() if self.reason_sel.value() == "Other" else self.reason_sel.value()
        self.win.db.add_due(self.rid, reason or "Other", amount, self.date_f.iso())
        self.win.toast(f"Added a due of {inr(amount)}.", "ok")
        self.win.refresh_all()
        return True


# ════════════════════════════════════════════════════════════════════════════
#  Mark as left
# ════════════════════════════════════════════════════════════════════════════
class MarkLeftDialog(Dialog):
    def __init__(self, win, renter_id: int, name: str):
        super().__init__(win, f"Mark {name} as left", "This keeps their history - you can reactivate them later.", 420)
        self.win, self.rid = win, renter_id
        self.date_f = DateField()
        self.date_f.set_iso(today_iso())
        self.body.addWidget(labeled("Left on", self.date_f))
        self.note_f = Field("e.g. Moved out, end of lease\u2026", multiline=True)
        self.body.addWidget(labeled("Reason (optional)", self.note_f))
        self.add_button("Cancel", "ghost")
        self.add_button("Mark as left", "danger", self._confirm, close=False, icon="log-out")

    def _confirm(self):
        self.win.db.set_status(self.rid, "left", self.date_f.iso(), self.note_f.text().strip())
        self.win.toast("Marked as left.", "ok")
        self.win.refresh_all()
        return True


# ════════════════════════════════════════════════════════════════════════════
#  Settings
# ════════════════════════════════════════════════════════════════════════════
class SettingsDialog(Dialog):
    def __init__(self, win):
        super().__init__(win, "Settings", "", 440)
        self.win = win

        self.body.addWidget(label("Appearance", 12, W_SEMI, "text3"))
        seg_wrap = QHBoxLayout()
        self.theme_seg = Segmented(["Light", "Dark"])
        self.theme_seg.set_index(1 if Theme.dark() else 0, animate=False, emit=False)
        self.theme_seg.changed.connect(lambda i: win.set_theme("dark" if i == 1 else "light"))
        seg_wrap.addWidget(self.theme_seg)
        seg_wrap.addStretch()
        w1 = TWidget()
        w1.setLayout(seg_wrap)
        self.body.addWidget(w1)

        motion_row = QHBoxLayout()
        motion_row.addWidget(label("Interface animations", 14))
        motion_row.addStretch()
        self.motion_sw = Switch()
        self.motion_sw.setChecked(Motion.on)
        self.motion_sw.toggled.connect(win.set_motion)
        motion_row.addWidget(self.motion_sw)
        w2 = TWidget()
        w2.setLayout(motion_row)
        self.body.addWidget(w2)

        self.body.addWidget(label("WhatsApp", 12, W_SEMI, "text3"))
        self.cc_f = Field("91", kind="units")
        self.cc_f.setFixedWidth(120)
        self.cc_f.setText(win.db.get_setting("country_code", "91"))
        self.body.addWidget(labeled("Default country code", self.cc_f,
                                     "Used when a saved number doesn't already include one."))

        self.body.addWidget(label("Data", 12, W_SEMI, "text3"))
        drow = QHBoxLayout()
        drow.setSpacing(10)
        dcol = QVBoxLayout()
        dcol.setSpacing(2)
        dcol.addWidget(label("Photos, Aadhaar cards and the database all live here.", 12.5, tone="text2", wrap=True))
        dcol.addWidget(label(str(DATA_DIR), 11.5, tone="text3", wrap=True, selectable=True))
        drow.addLayout(dcol, 1)
        openf = Btn("", "icon", "folder", "sm")
        openf.setFixedSize(34, 34)
        openf.setToolTip("Open data folder")
        openf.clicked.connect(lambda: open_folder(DATA_DIR))
        drow.addWidget(openf, 0, Qt.AlignmentFlag.AlignTop)
        w3 = TWidget()
        w3.setLayout(drow)
        self.body.addWidget(w3)

        self.add_button("Done", "ink", self._save)

    def _save(self):
        self.win.db.set_setting("country_code", digits(self.cc_f.text()) or "91")


# ════════════════════════════════════════════════════════════════════════════
#  Main window
# ════════════════════════════════════════════════════════════════════════════
class MainWindow(QWidget):
    def __init__(self):
        super().__init__()
        self.db = Database()
        self.overlays: list = []
        self.toasts: list = []
        self.home: HomePage | None = None
        self.profile: ProfilePage | None = None

        saved_theme = self.db.get_setting("theme", "light")
        Theme.mode = saved_theme if saved_theme in PALETTES else "light"
        Motion.on = self.db.get_setting("motion", "1") != "0"
        QApplication.instance().setStyleSheet(build_qss())

        self.setWindowTitle(APP_NAME)
        self.resize(1340, 880)
        self.setMinimumSize(940, 620)

        self.root = QVBoxLayout(self)
        self.root.setContentsMargins(0, 0, 0, 0)
        self.root.setSpacing(0)
        self.topbar_slot = QVBoxLayout()
        self.topbar_slot.setSpacing(0)
        self.root.addLayout(self.topbar_slot)
        self.host = PageHost()
        self.root.addWidget(self.host, 1)

        self._build_ui(first=True)
        QShortcut(QKeySequence("Ctrl+N"), self, activated=self.open_add_renter)
        QShortcut(QKeySequence("Ctrl+,"), self, activated=self.open_settings)

    # -- (re)build everything theme-sensitive --------------------------------------------------
    def _build_ui(self, first: bool = False):
        keep_rid = None if first else (self.profile.rid if self.profile else None)
        on_profile = (not first) and self.host.current is self.profile

        while self.topbar_slot.count():
            item = self.topbar_slot.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        self.topbar_slot.addWidget(self._make_topbar())

        for child in list(self.host.findChildren(QWidget)):
            if child.parent() is self.host:
                child.setParent(None)
                child.deleteLater()
        self.host.pages = []
        self.home = HomePage(self)
        self.profile = ProfilePage(self)
        self.host.add(self.home)
        self.host.add(self.profile)

        self.setStyleSheet(f"background:{Theme.hex('bg')};")
        if on_profile and keep_rid is not None and self.db.get_renter(keep_rid):
            self.profile.open(keep_rid, push=False)
            self.host.show_page(self.profile, fade=False)
        else:
            self.host.show_page(self.home, fade=False)
        self.home.load(animate=False)

    def _make_topbar(self) -> QWidget:
        bar = TWidget()
        bar.setFixedHeight(66)
        tb = QHBoxLayout(bar)
        tb.setContentsMargins(24, 0, 20, 0)
        tb.setSpacing(10)
        tb.addWidget(IconTile("key", "ink", 34))
        tcol = QVBoxLayout()
        tcol.setSpacing(0)
        tcol.addWidget(label(APP_NAME, 16.5, W_BOLD, display=True))
        tb.addLayout(tcol)
        tb.addStretch()
        theme_btn = Btn("", "icon", "sun" if Theme.dark() else "moon", "sm")
        theme_btn.setFixedSize(36, 36)
        theme_btn.setToolTip("Switch to light" if Theme.dark() else "Switch to dark")
        theme_btn.clicked.connect(lambda: self.set_theme("light" if Theme.dark() else "dark"))
        tb.addWidget(theme_btn)
        settings_btn = Btn("", "icon", "sliders", "sm")
        settings_btn.setFixedSize(36, 36)
        settings_btn.setToolTip("Settings")
        settings_btn.clicked.connect(self.open_settings)
        tb.addWidget(settings_btn)
        tb.addSpacing(4)
        add_btn = Btn("Add renter", "ink", "plus", "sm")
        add_btn.clicked.connect(self.open_add_renter)
        tb.addWidget(add_btn)
        wrap = QVBoxLayout()
        wrap.setContentsMargins(0, 0, 0, 0)
        wrap.setSpacing(0)
        wrap.addWidget(bar)
        wrap.addWidget(Divider())
        holder = TWidget()
        holder.setLayout(wrap)
        return holder

    # -- navigation -----------------------------------------------------------------------
    def open_profile(self, rid: int, _record: bool = True):
        self.profile.open(rid, push=_record)
        self.host.show_page(self.profile)

    def go_home(self):
        self.host.show_page(self.home)
        self.home.load()

    # -- actions used throughout the app ---------------------------------------------------------
    def open_add_renter(self):
        d = RenterFormDrawer(self, None)
        d.saved.connect(lambda rid: self.refresh_all())
        d.open()

    def open_edit_renter(self, rid: int):
        d = RenterFormDrawer(self, rid)
        d.saved.connect(lambda rid: self.refresh_all())
        d.open()

    def open_send_rent(self, rid: int):
        SendRentDrawer(self, rid).open()

    def open_export(self, rids: list[int] | None):
        ExportDialog(self, rids).open()

    def open_add_due(self, rid: int):
        AddDueDialog(self, rid).open()

    def open_settings(self):
        SettingsDialog(self).open()

    def quick_toggle_status(self, rid: int):
        r = self.db.get_renter(rid)
        if not r:
            return
        if r["status"] == "active":
            MarkLeftDialog(self, rid, r["name"]).open()
        else:
            self.db.set_status(rid, "active")
            self.toast(f"{r['name']} is marked active again.", "ok")
            self.refresh_all()

    def confirm_delete_renter(self, rid: int, after=None):
        r = self.db.get_renter(rid)
        if not r:
            return
        dlg = Dialog(self, f"Delete {r['name']}?",
                     "This permanently removes their profile, photos, dues and bill history. "
                     "This can't be undone.", 420)
        dlg.add_button("Cancel", "ghost")

        def do_delete():
            self.db.delete_renter(rid)
            self.toast(f"Deleted {r['name']}.", "ok")
            self.refresh_all()
            if after:
                after()
            return True
        dlg.add_button("Delete permanently", "danger", do_delete, close=False, icon="trash")
        dlg.open()

    def refresh_all(self):
        if self.home is not None:
            self.home.load(animate=False)
        if self.profile is not None and self.host.current is self.profile and self.profile.rid is not None:
            if self.db.get_renter(self.profile.rid):
                self.profile.load()
            else:
                self.go_home()

    # -- settings -------------------------------------------------------------------------------
    def set_theme(self, mode: str):
        if mode not in PALETTES or Theme.mode == mode:
            return
        for ov in list(self.overlays):
            ov.hide()
        self.overlays.clear()
        for t in list(self.toasts):
            t.deleteLater()
        self.toasts.clear()
        Theme.mode = mode
        self.db.set_setting("theme", mode)
        QApplication.instance().setStyleSheet(build_qss())
        self._build_ui()

    def set_motion(self, on: bool):
        Motion.on = on
        self.db.set_setting("motion", "1" if on else "0")

    # -- toasts -----------------------------------------------------------------------------------
    def toast(self, text: str, kind: str = "ok", action_text: str = "", action=None):
        t = Toast(self, text, kind, action_text, action)
        t.show()
        t.raise_()
        self.toasts.append(t)
        self._reflow_toasts(new=t)
        QTimer.singleShot(4200, lambda: self.drop_toast(t))

    def drop_toast(self, t):
        if t not in self.toasts:
            return
        self.toasts.remove(t)

        def done():
            try:
                t.deleteLater()
            except RuntimeError:
                pass
            self._reflow_toasts()
        fade_out(t, 160, done)

    def _reflow_toasts(self, new=None):
        y = self.height() - 24
        for t in reversed(self.toasts):
            try:
                x = self.width() - t.width() - 24
                y -= t.height()
                if t is new:
                    t.move(x, y + 14)
                    fade_in(t, 220, dy=14)
                elif Motion.on:
                    a = QPropertyAnimation(t, b"pos", t)
                    a.setDuration(200)
                    a.setEasingCurve(EASE_OUT)
                    a.setStartValue(t.pos())
                    a.setEndValue(QPoint(x, y))
                    a.start(QAbstractAnimation.DeletionPolicy.DeleteWhenStopped)
                else:
                    t.move(x, y)
                y -= 10
            except RuntimeError:
                pass

    def resizeEvent(self, e):
        super().resizeEvent(e)
        for ov in self.overlays:
            try:
                ov.setGeometry(self.rect())
                ov.layout_content()
            except RuntimeError:
                pass
        self._reflow_toasts()

    def closeEvent(self, e):
        try:
            self.db.conn.close()
        except Exception:
            pass
        super().closeEvent(e)


def excepthook(etype, value, tb):
    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(LOG_PATH, "a", encoding="utf-8") as f:
        f.write(f"\n[{now_iso()}]\n")
        traceback.print_exception(etype, value, tb, file=f)
    traceback.print_exception(etype, value, tb, file=sys.stderr)


def main():
    sys.excepthook = excepthook
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setStyle("Fusion")
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
