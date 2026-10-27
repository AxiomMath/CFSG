module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofLA7
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem step1515R_of_named (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple)
    (hHJA7 : Step1515HJListA7) (hcov : Step1515HJListCover) (hV : Step1515HJV)
    (hEnd : Step1515HJEnd) (hL325 : Step1515LA7L325) (hY0 : Step1515LA7Y0)
    (hsimp : Step1515LA7Simple) : Step1515R :=
  step1515R_of h131 h137 hcl h1511 h1512 h1513 h156 (step1515A7Trans_of h148 hbot)
    (step1515A7Omega_of h148 hbot h131 h135) (step1515M22_of h148 hbot h142)
    (step1515LA7_of h148 hbot hL325 hY0 hsimp)
    (step1515HJList_of_items h148 hbot h142 h134 h48 h135s hHJA7 hcov) (step1515HJ_of hV hEnd)

end CFSG.RankThree.PartTwo.Sec15
