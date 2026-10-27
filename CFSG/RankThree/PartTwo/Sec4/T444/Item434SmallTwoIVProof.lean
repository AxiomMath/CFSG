module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVSp82
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU52
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVO8p
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU58

public section

namespace CFSG.RankThree.PartTwo.Sec4

section Families

theorem item434SmallTwoIV_of (hT : Census.TripleCoverLie) (hU62 : Item434SmallTwoIV_U62_27)
    (hO8 : Item434SmallTwoIV_O8p_27Outer) (hF4 : Item434SmallTwoIV_F42_27)
    (hU48 : Item434SmallTwoIV_U48_27) : Item434SmallTwoIV :=
  item434SmallTwoIV_of_parts item434SmallTwoIV_Sp82 (item434SmallTwoIV_U52_of hT)
    (item434SecFor_of_card item434SmallTwoIV_U62_9 hU62) (item434SmallTwoIV_O8p_of hO8)
    (item434SecFor_of_card (item434SmallTwoIV_F42_9_of hT) hF4)
    (item434SecFor_of_card item434SmallTwoIV_U48_9 hU48) (item434SmallTwoIV_U58_of hT)

end Families

end CFSG.RankThree.PartTwo.Sec4
