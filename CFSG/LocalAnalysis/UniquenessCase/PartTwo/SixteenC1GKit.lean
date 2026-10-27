module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitG

variable {W : Type} [CommGroup W]

@[expose] def OmegaPlaneE9 (H : Subgroup (MulAut W)) : Prop :=
  ∀ P : Subgroup W, Nat.card P = 4 → (∀ w ∈ P, w ≠ 1 → Nat.card (ptCent H w) = 960) →
    ∃ E : Subgroup (MulAut W), E ≤ H ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧ StableUnder E P

end KitG

@[expose] def OmegaKitG : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 → OmegaPlaneE9 H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
