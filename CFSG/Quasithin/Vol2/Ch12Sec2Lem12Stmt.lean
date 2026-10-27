module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stmt12_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp1223 G T L V) (v : G),
    v ∈ V → v ≠ 1 → IsSylowTwoOf (h.Tv v) (h.Mv v) →
    pCoreOf 2 (autOn (h.Lv v ⊔ h.Tv v) V) = ⊥ →
      (h.Q = pCoreOf 2 (h.Lv v ⊔ h.Tv v) ∧
        IsSylowTwoOf h.Q (centralizerSection (h.Gv v) (h.Lv v) (pCoreOf 2 (h.Lv v))) ∧
        HypC23 (h.Gv v) h.Q (h.Mv v)) ∧
      (autOn (h.Lv v) V = perfectCore (autOn (h.Lv v) V) → V = ⁅V, h.Lv v⁆ →
        HypC28 (h.Gv v) h.Q (h.Mv v) (perfectCore (h.Lv v)) V)

end CFSG.Quasithin.H13
