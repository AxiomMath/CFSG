module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

namespace Data

variable {G : Type} [Group G] [Finite G]

theorem k_eq_two_iff (D : Data G) :
    D.k = 2 ↔ ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  by_cases h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M <;> simp [h]

end Data

end CFSG.LocalAnalysis.UniquenessCase.UC22
