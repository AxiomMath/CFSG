module

public import CFSG.RankThree.PartTwo.Sec4.Census.FromTheoremThree
public import CFSG.RankThree.PartOne.Census3.OpenCases
import CFSG.RankThree.PartOne.Census3.Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3
open CFSG.RankThree.PartTwo.Census (BridgeSp6Four BridgeSp8Two BridgeOmega8PlusTwo
  BridgeOmega8MinusTwo)

theorem rank3II_4_2_of_open (hspin : SpinRankFour) (hB : RankFourBabyMonster)
    (hSp6 : BridgeSp6Two) (hSp64 : BridgeSp6Four)
    (hSp8 : BridgeSp8Two) (hOp : BridgeOmega8PlusTwo) (hOm : BridgeOmega8MinusTwo)
    (hlarge : SpinLargePrimeRankThree) : Item4_2 := by
  intro G _ _ hG hs hnonab
  have : IsSimpleGroup G := hs
  exact list42_of_theoremThreeList hG hSp6 hSp64 hSp8 hOp hOm hlarge
    (theorem_three_catalog_of_spin hspin hB G hnonab hG.kGroup
      (SectionFourHyp.twoLocalOddRank_le hG))

end CFSG.RankThree.PartTwo.Sec4.Census
