module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.B5

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def AsB492Split : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ n : ℕ, (n = 4 ∨ n = 5) →
    ∀ (L : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n (ZMod 2)) →* ↥L),
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L U ⊥ π →
      ((FFModel.nat (StatedSL n (ZMod 2))).RealizesVia L ⊤ U π ∨
        (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia L ⊤ U π) →
      (∃ A : Subgroup (MulAut V), IsFFStarOffender L A ∧ IsQuadratic A) →
      ∃ X : Subgroup V, (∀ l ∈ L, ∀ x ∈ X, l x ∈ X) ∧ IsIntDirect U X ⊤

end CFSG.Quasithin.B5
