module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Census

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {X : Type} [Group X] [Finite X]

theorem sectionFourHyp_of_rankHyp (h : RankHyp X) :
    CFSG.RankThree.PartTwo.SectionFourHyp X where
  kGroup := h.kGroup
  evenRank_le := CFSG.RankThree.PartTwo.Sec4.Census.evenRank_le_of_localRank_le
    fun p hp hp2 => by
      by_cases hp3 : p = 3
      · subst hp3
        exact (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank 3 hp X).trans
          h.rank_three
      · have h3 : 3 < p := by
          have h2 := hp.two_le
          rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 4 < p by omega) with h' | h' | h' | h'
          · exact absurd h' hp2
          · exact absurd h' hp3
          · subst h'
            norm_num at hp
          · omega
        exact (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp X).trans
          ((h.rank_prime p hp h3).trans (by norm_num))
  localRank_lt p hp hp3 :=
    ((CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp X).trans
      (h.rank_prime p hp hp3)).trans_lt (by norm_num)

theorem list42_of_rankHyp
    (h : RankHyp X) : Sec4.Census.List42 (X ⧸ Subgroup.center X) :=
  CFSG.RankThree.PartTwo.Sec4.RonanK432.list42_quotient_center h.quasisimple
    (sectionFourHyp_of_rankHyp h)

end CFSG.RankThree.PartTwo.Sec19.SimsC198
