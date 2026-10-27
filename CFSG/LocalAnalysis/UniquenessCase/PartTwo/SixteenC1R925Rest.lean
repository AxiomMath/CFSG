module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925KGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.L3Prime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.U3Prime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Blueprint (LieModel)

set_option linter.unusedSectionVars false

@[expose] def OddIdxPropL3U3Rest : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), (2 ≤ f ∨ p = 2) →
    (p ^ f % 3 = 2 ∧ LieModel K .PSL 3 p f ∨ p ^ f % 3 = 1 ∧ LieModel K .PSU 3 p f) →
      OddIdxProp K

section Certified


theorem oddIdxPropL3U3_of_rest (h : OddIdxPropL3U3Rest) : OddIdxPropL3U3 := by
  intro K _ _ p f hh
  have hpf : p.Prime ∧ 1 ≤ f := by
    rcases hh with ⟨-, hL⟩ | ⟨-, hU⟩
    · exact ⟨hL.admissible.1, hL.admissible.2.1⟩
    · exact ⟨hU.admissible.1, hU.admissible.2.1⟩
  by_cases hc : f = 1 ∧ p ≠ 2
  · obtain ⟨hf1, hp2⟩ := hc
    subst hf1
    rcases hh with ⟨h3, hL⟩ | ⟨h3, hU⟩
    · exact OddIdx.oddIdxProp_psl3_prime hpf.1 hp2 (by simpa using h3) (by simpa using hL)
    · exact OddIdx.oddIdxProp_psu3_prime hpf.1 hp2 (by simpa using h3) (by simpa using hU)
  · refine h K p f ?_ hh
    by_cases hp2 : p = 2
    · exact Or.inr hp2
    · left
      by_contra hlt
      exact hc ⟨by omega, hp2⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
