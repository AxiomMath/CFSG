module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section KitE16

variable {W : Type} [CommGroup W]

@[expose] def OmegaE16Sing (H : Subgroup (MulAut W)) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ H → IsElemAbelian2 E → Nat.card E = 16 →
    ∃ z : W, z ≠ 1 ∧ ∃ P : Subgroup W, P.index = 2 ∧
      (∀ w : W, (∀ e ∈ E, e w = w) ↔ (w = 1 ∨ w = z)) ∧
      (∀ e ∈ E, ∀ w ∈ P, e w = w ∨ e w = w * z) ∧
      (∀ e ∈ E, e ≠ 1 → ∀ w : W, (e w = w ∨ e w = w * z) → w ∈ P) ∧
      P ≤ Subgroup.closure {w : W | ∃ e ∈ E, e ≠ 1 ∧ e w = w} ∧
      ∃ e ∈ E, ∃ w ∈ P, e w ≠ w

end KitE16

@[expose] def OmegaKitE16 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)),
    NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1 → OmegaE16Sing H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
