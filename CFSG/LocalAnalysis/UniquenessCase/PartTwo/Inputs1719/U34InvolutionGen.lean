module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_U34InvolutionGen : Prop :=
  ∀ (X : Type) [Group X], IsU3 X 2 → ∀ α : MulAut X, α * α = 1 → α ≠ 1 →
    ∃ x₁ x₂ : X, Subgroup.closure {(α x₁)⁻¹ * x₁, (α x₂)⁻¹ * x₂} = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
