module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Str
public import CFSG.Quasithin.H13.GoldschmidtC137Tail

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem isRankTwoLie2Derived :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.hhat.2.2))))

theorem toBaum : BaumCtx X T V L P :=
  ⟨h.hT, h.hprod, h.hL, h.hL2, Or.inl h.hLq, h.isRankTwoLie2Derived, h.hTP, h.hPX, h.hred,
    h.hVL, h.hB⟩

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137
