module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_pRank_le_evenRank (D : Data G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p D.M ≤ CFSG.Open.evenRank G :=
  CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1

theorem s16h_pRank_eq_three (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3)
    {p : ℕ} (hp : p ∈ D.sig) : CFSG.Open.pRank p D.M = 3 := by
  have hle := s16h_pRank_le_evenRank D (D.sig_prime p hp).1 (D.sig_prime p hp).2
  have h3 := S.hx.three_le p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
