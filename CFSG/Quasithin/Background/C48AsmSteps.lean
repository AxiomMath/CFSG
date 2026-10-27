module

public import CFSG.Quasithin.Background.C4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable (G : Type) [Group G] [Finite G]

@[expose] def C48SporStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Conclusion H R M L V K →
    (C31Case3 H R M L V K ∨ C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨
      C31Case6 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨
      C31Case9 H R M L V K) →
    (C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
        C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
        C48Case7 H R M L V K) ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 L) →
        IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 2

@[expose] def C48C41LineStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → K ∈ cComp H → CharTwo K →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → ¬ K ≤ M → C41Conclusion H R M L V K →
    (C41Case2 H R M L V K ∨ C41Case3 H R M L V K) → C48Case1 H R M L V K

@[expose] def C48C41FourStep : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → K ∈ cComp H → CharTwo K →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → ¬ K ≤ M → C41Conclusion H R M L V K →
    C41Case4 H R M L V K →
    C48Case2 H R M L V K ∧
      ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 L) →
        IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false k →
        k ≤ 4

end CFSG.Quasithin
