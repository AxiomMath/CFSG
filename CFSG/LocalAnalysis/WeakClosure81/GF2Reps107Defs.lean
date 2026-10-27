module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Lem10_7Irr : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : MulAut W), Is135Context Y L →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 → Subgroup.center ↥L ≠ ⊥ →
      t ∈ Y → orderOf t = 2 → E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 →
        (∃ (S : Type) (_ : Group S), LieModel S .PSU 4 3 1 ∧ IsHat ↥L S) ∧ rk W = 12

@[expose] def W4Lem10_7Fin : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (t : MulAut W), Is135Context Y L →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 → Nat.card (Subgroup.center ↥L) = 3 →
      (∀ z ∈ Subgroup.center ↥L, t * (z : MulAut W) = (z : MulAut W) * t) → rk W ≤ 57 →
      t ∈ Y → orderOf t = 2 → E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 → rk W = 12

end CFSG.LocalAnalysis.WeakClosure81
