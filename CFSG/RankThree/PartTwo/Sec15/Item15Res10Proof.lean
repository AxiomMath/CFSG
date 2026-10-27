module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofV
public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofEnd
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7Proof
public import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

theorem step1515R_of_res10 (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (h155 : Item155wR) (hFX : Step1515HJEndFpfX)
    (hFT : Step1515HJEndFpfT0) (hθ : KL325ThetaCent) (hK325 : KL325SubgroupOrder) :
    Step1515R :=
  step1515R_of_res3 h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s h153
    hobs h149 h1411 hloc h1444 h146 hc142 h152 hgen
    (step1515HJD_of_res7 h134 h48 hloc h152 h153 h155) step1515HJVTail_of_res10
    (step1515HJEndTail_of_res7 h134 h48 h152 h153 h155 hFX hFT) hθ hK325

theorem step1515R_of_core (h131 : Item131) (h137 : Item137) (hcl : Claim1515M12)
    (h1511 : Item1511R) (h1512 : Item1512R) (h1513 : Item1513R) (h156 : Item156R)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h135 : Item135) (h135s : Item135Simple) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h149 : Sec16.Item149S14) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h1444 : Item1444S14) (h146 : Item146S14) (hc142 : Concl142R)
    (h152 : Item152R) (hgen : KS1517Gen) (h155 : Item155wR) (hC : Step1515HJEndFpfRCore)
    (hθ : KL325ThetaCent) (hK325 : KL325SubgroupOrder) : Step1515R :=
  step1515R_of_res10 h131 h137 hcl h1511 h1512 h1513 h156 h148 hbot h142 h134 h48 h135 h135s
    h153 hobs h149 h1411 hloc h1444 h146 hc142 h152 hgen h155
    (step1515HJEndFpfX_of_core h152 h153 hC) (step1515HJEndFpfT0_of_core h152 h153 hC) hθ hK325

end CFSG.RankThree.PartTwo.Sec15
