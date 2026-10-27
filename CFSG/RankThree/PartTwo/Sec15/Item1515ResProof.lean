module

public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofA7
public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofLA7
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem step1515R_of_res (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (haut : KS1515A7Aut) (hJ2 : KS1515J2NoA7)
    (hV : Step1515HJV) (hEnd : Step1515HJEnd) (hgen325 : Step1515LA7L325Gen) : Step1515R :=
  step1515R_of_named h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s
    (step1515HJListA7_of h142 haut hJ2)
    (step1515HJListCover_of h142 h134 h48 h135s (step1515HJ_of hV hEnd)) hV hEnd
    (step1515LA7L325_of h153 hobs h149 h1411 hloc hgen325)
    (step1515LA7Y0_of h153 hobs h1411 h1444 h146 hbot hc142)
    (step1515LA7Simple_of h135s hc142 h152 h1511 hgen)

end CFSG.RankThree.PartTwo.Sec15
