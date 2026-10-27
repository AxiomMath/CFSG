module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def RSp6SmallMod : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (U : Subgroup W), IsSpn ↥H 6 1 → U ≠ ⊥ →
      commSub U H = U → E3.mQuot U (U ⊓ fixV H) ≤ 8 →
        (rk ↥U = 8 ∧ U ⊓ fixV H = ⊥ ∧ IsIrrOn H U ⊥) ∨
          (E3.mQuot U (U ⊓ fixV H) = 6 ∧ rk ↥(U ⊓ fixV H) ≤ 1)

@[expose] def RSp6SpinCent : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ H : Subgroup (MulAut W), IsSpn ↥H 6 1 → rk ↥(⊤ : Subgroup W) = 8 → IsIrrOn H ⊤ ⊥ →
      ∀ c : MulAut W, (∀ h ∈ H, c * h = h * c) → c = 1

@[expose] def RSp6SpinForm : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ H : Subgroup (MulAut W), IsSpn ↥H 6 1 → rk ↥(⊤ : Subgroup W) = 8 → IsIrrOn H ⊤ ⊥ →
      ∃ Q : W → ZMod 2, IsPlusQuadF2 Q ∧ QuadInvariant Q H

@[expose] def RSp6SpinStab : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ H : Subgroup (MulAut W), IsSpn ↥H 6 1 → rk ↥(⊤ : Subgroup W) = 8 → IsIrrOn H ⊤ ⊥ →
      ∀ Q : W → ZMod 2, IsPlusQuadF2 Q → QuadInvariant Q H →
        (∀ w : W, w ≠ 1 → Q w = 0 → IsE64L3 ↥(ptCent H w)) ∧
          ∀ w : W, Q w ≠ 0 → IsG2Two ↥(ptCent H w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
