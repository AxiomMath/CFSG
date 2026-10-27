module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitD

variable {W : Type} [CommGroup W]

@[expose] def OmegaAxisBound (H : Subgroup (MulAut W)) : Prop :=
  ∀ Q : W → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q H →
    ∀ E : Subgroup (MulAut W), E ≤ normalizer (H : Set (MulAut W)) → IsElemAbelian2 E →
      ∀ P : Subgroup W, P.index = 2 → ∀ t ∈ E, t ≠ 1 → (∀ p ∈ P, t p = p) →
        (∀ e ∈ E, ∀ u ∈ P, Q (e u * u⁻¹) = 0) → Nat.card E ≤ 4

end KitD

@[expose] def OmegaKitD : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 → OmegaAxisBound H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
