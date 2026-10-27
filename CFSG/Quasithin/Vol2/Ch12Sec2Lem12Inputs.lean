module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Lem12212Comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp1223 G T L V) (v : G),
    v ∈ V → v ≠ 1 → IsSylowTwoOf (h.Tv v) (h.Mv v) →
    pCoreOf 2 (autOn (h.Lv v ⊔ h.Tv v) V) = ⊥ →
    autOn (h.Lv v) V = perfectCore (autOn (h.Lv v) V) → V = ⁅V, h.Lv v⁆ →
      perfectCore (h.Lv v) ∈ cComp (h.Mv v)

end CFSG.Quasithin.H13
