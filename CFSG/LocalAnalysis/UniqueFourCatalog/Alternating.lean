module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
import CFSG.RankThree.PartTwo.Census.Alternating
import CFSG.LocalAnalysis.SectionRank.Alternating

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

theorem Standing4.false_of_alternating {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    {n : ℕ} (e : G ≃* alternatingGroup (Fin n)) : False := by
  rcases le_or_gt n 8 with h8 | h9
  · exact hS.false_of_pRank_le_two e fun r hr hr2 =>
      CFSG.SectionRank.pRank_alternating_le_two h8 hr hr2
  · exact hS.false_of_not_isCharTwoType e
      (CFSG.RankThree.PartTwo.Census.not_isCharTwoType_alternating h9)

end CFSG.Yardstones.Mf4cdcdf2e013
