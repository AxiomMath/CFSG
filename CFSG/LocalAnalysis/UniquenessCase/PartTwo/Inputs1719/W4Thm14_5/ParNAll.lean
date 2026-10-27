module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

@[expose] def KNatParNAll : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H S P : Subgroup (MulAut W)) (k n : ℕ),
    IsNaturalClassicalModule H k → 2 ≤ k → ⁅H, H⁆ = H → IsSylowIn 2 S H →
    H ⊓ normalizer (S : Set (MulAut W)) ≤ P → P ≤ H → commSub (fixV S) (Hinf P) ≠ ⊥ →
    NParam (Hinf P) n → n = k ∨ (IsOmegaMinus ↥H 4 k ∧ n = 2 * k)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
