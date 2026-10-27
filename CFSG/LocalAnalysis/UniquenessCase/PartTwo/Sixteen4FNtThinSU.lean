module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallUnitarySolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

theorem s16nt_range_su {n : ℕ} (hq : CFSG.Open.IsQuasisimple Y)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsSUn Y n 1) : 4 ≤ n := by
  by_contra hlt
  have hn : n ≤ 3 := by omega
  exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq
    (s16low_isSolvable_of_isSUn_le_three hn h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
