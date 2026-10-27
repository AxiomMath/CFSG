module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857Final
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem r858_of_r857
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) (h857 : R857 D) :
    R858 D := by
  intro L Q P hcex
  exact normal_or_ncard_two_of_list857 hcex.mem hcex.rank (h857 L Q P hcex).1
    (CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp hSg
      hcex.notStrong hcex.mem)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
