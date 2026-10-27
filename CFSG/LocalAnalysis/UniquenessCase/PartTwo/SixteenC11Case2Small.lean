module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16c11_pRank_three_le_two_of_small {A : Type} [Group A] [Finite A]
    {K L₀ X : Subgroup A} (hI : IsInternalDirect K L₀ X) (hK : IsSym ↥K 3)
    (hL : IsSym ↥L₀ 5 ∨ IsLn ↥L₀ 3 1) : CFSG.Open.pRank 3 X ≤ 2 := by
  by_contra h
  refine s16c13bcA_false_of_three_le_pRank hI ?_ ?_ (not_le.1 h)
  · rw [s16c1610_card_of_isSym hK]
    rfl
  · rcases hL with hL | hL
    · left
      rw [s16c1610_card_of_isSym hL]
      rfl
    · exact Or.inr (s16c13bcA_card_isLn_three hL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
