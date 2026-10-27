module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypes
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem claim153TwinCase7_of_item148R
    (h148 : Item148R) :
    Claim153TwinCase7 := by
  intro G _ _ A c L hR Y _ _ M hM _ _ h7
  have h := hR.toSec14Std
  exact Proof15Res6.false_of_case148Seven_two h (h148 G A c L hR)
    (facts_of_mem_maximalTwoLocalsContaining h hM).2.2.1 h7

end CFSG.RankThree.PartTwo.Sec15
