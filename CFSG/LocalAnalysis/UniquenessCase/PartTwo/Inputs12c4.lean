module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def ClassicalEvenAltG2Der (X : Type) [Group X] : Prop :=
  F12.ClassicalEvenAltG2 X ∨ ∃ n : ℕ, F08.IsG2Der X n

@[expose] def W4Thm12McClurg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T V L : Subgroup G),
    CFSG.Open.IsKGroup ↥M → CFSG.ABGLocalTools.IsSylowOf 2 T M →
    InCalV M V → TwoReduced M V → F12.IsComponentModO2 M L → ⁅L, V⁆ ≠ ⊥ →
    ¬ ⁅F12.jOf T, L⁆ ≤ pCoreOf 2 L → ClassicalEvenAltG2Der (Bar2 L)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
