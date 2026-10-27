module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item42
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43
public import CFSG.RankThree.PartTwo.Sec4.Census.Item46
import CFSG.RankThree.PartOne.Census3.Sporadic
import CFSG.RankThree.PartTwo.Census.Exceptional.Main

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3 TauCeti
open CFSG.RankThree.PartTwo.Census (BridgeSp6Four BridgeSp8Two BridgeOmega8PlusTwo
  BridgeOmega8MinusTwo)

theorem rank3II_4_3_of_inputs (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) (hU62 : TripleCoverU62RankFour) (hspin : SpinRankFour) :
    Item4_3 :=
  rank3II_4_3_of_open h41 hmult hSuz hU62 hspin
    CFSG.RankThree.PartTwo.Census.Exceptional.exceptionalRankFour excludedIndex_Fi22
    excludedIndex_Fi24Prime

theorem rank3II_4_6_of_inputs (h41 : Item4_1) (hspin : SpinRankFour) (hB : RankFourBabyMonster)
    (hSp6 : BridgeSp6Two) (hSp64 : BridgeSp6Four) (hSp8 : BridgeSp8Two) (hOp : BridgeOmega8PlusTwo)
    (hOm : BridgeOmega8MinusTwo) (hlarge : SpinLargePrimeRankThree)
    (hmult : TripleCoverInputs) (hSuz : TripleCoverSuzRankFour) (hU62 : TripleCoverU62RankFour)
    (hin : Inputs46) : Item4_6 :=
  rank3II_4_6_of h41 (rank3II_4_2_of_open hspin hB hSp6 hSp64 hSp8 hOp hOm hlarge)
    (rank3II_4_3_of_inputs h41 hmult hSuz hU62 hspin) hin

end CFSG.RankThree.PartTwo.Sec4.Census
