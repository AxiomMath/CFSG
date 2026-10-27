module

public import CFSG.Quasithin.H13.GoldschmidtC137S6ToC
public import CFSG.Quasithin.H13.GoldschmidtC137CBase
public import CFSG.Quasithin.H13.GoldschmidtC137S6Base

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)

include h in
theorem toBase : C137Base X T V L P :=
  ⟨h.hT, h.hTP, h.hPX, h.hred, h.hVe, h.hLX, h.hXN, h.hRT, pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2, fun _ ha => h.hQR (h.CXV ▸ ⟨h.hT.1 ha.1, ha.2⟩), h.toBaum⟩

end S6Ctx

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M}

abbrev toC137B (F : S6Frame h) : C137FrameB h.toBase := F.toC137

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
