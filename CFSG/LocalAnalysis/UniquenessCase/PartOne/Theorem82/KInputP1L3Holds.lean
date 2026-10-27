module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Classical
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3NotOrth

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

set_option linter.unusedSectionVars false


theorem l3NotEvenClassical_holds : L3NotEvenClassical := by
  intro X _ _ _ ℓ f h
  obtain ⟨hp, hf, c, hc, hcard⟩ := card_of_lieModel_three h
  have hq3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
    rcases h with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
  refine ⟨not_isOrthogonalTwo ?_ hc hcard, fun hℓ => ?_⟩
  · by_cases h2 : ℓ = 2
    · subst h2
      exact Or.inr ⟨f, hf, rfl⟩
    · exact Or.inl (odd_five_le_pow hp hf h2 hq3)
  · obtain ⟨hodd, h5⟩ := odd_five_le_pow hp hf hℓ hq3
    exact not_isClassicalTwoOrG2_of_order
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part hodd h5 hc hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
