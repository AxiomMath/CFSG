module

public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProof
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofA7Aut
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofJ2
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem step1515HJListA7_of_item142
    (h142 : Item142R) : Step1515HJListA7 :=
  step1515HJListA7_of h142 ks1515A7Aut ks1515J2NoA7

theorem step1515R_of_res2 (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (hV : Step1515HJV) (hEnd : Step1515HJEnd)
    (hgen325 : Step1515LA7L325Gen) : Step1515R :=
  step1515R_of_res h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s h153
    hobs h149 h1411 hloc h1444 h146 hc142 h152 hgen ks1515A7Aut ks1515J2NoA7 hV hEnd hgen325

theorem step1515R_of_tails (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (hD : Step1515HJD) (hVT : Step1515HJVTail)
    (hET : Step1515HJEndTail) (hgen325 : Step1515LA7L325Gen) : Step1515R :=
  step1515R_of_res2 h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s h153
    hobs h149 h1411 hloc h1444 h146 hc142 h152 hgen (step1515HJV_of_tail hD hVT)
    (step1515HJEnd_of_tail hD hET) hgen325

end CFSG.RankThree.PartTwo.Sec15
