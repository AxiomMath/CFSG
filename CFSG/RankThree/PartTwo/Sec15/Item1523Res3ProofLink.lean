module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofL2
public import CFSG.RankThree.PartTwo.Sec15.Item153Push2Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13


theorem step153ListedL2R_of_item148R_main
    (h148 : Sec14.Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) : Step153ListedL2R :=
  step153ListedL2R_of_item148R h148 h134 h48

theorem step153PushListedR_of_item148R
    (h148 : Sec14.Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) : Step153PushListedR :=
  step153PushListedR_of_L2 (step153ListedL2R_of_item148R_main h148 h134 h48)

end CFSG.RankThree.PartTwo.Sec15
