module

public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_32_L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ T ≤ Subgroup.normalizer (K : Set G) →
      (∀ n : ℕ, ¬ IsPSL 2 2 n (cStar K)) ∧ ¬ IsAlt 5 (cStar K)

end CFSG.Quasithin.H13.L32A.C
