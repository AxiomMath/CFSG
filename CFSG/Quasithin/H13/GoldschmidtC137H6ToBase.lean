module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Base
public import CFSG.Quasithin.H13.GoldschmidtC137H6ToC
public import CFSG.Quasithin.H13.GoldschmidtC137CBase

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)

include h in
theorem toBase : C137Base X T V L P :=
  ⟨h.hT, h.hTP, h.hPX, h.hred, h.hVe, h.hLX, h.hXN, h.hRT, h.hQT, h.hTCR, h.toBaum⟩

end H6Ctx

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P}

abbrev toC137B (F : H6Frame h) : C137FrameB h.toBase := F.toC137

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
