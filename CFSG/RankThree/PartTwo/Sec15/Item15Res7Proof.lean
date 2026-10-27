module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4Proof
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

section HJ

theorem step1515HJD_of_res7 (h134 : Item134) (h48 : Sec4.Item4_8) (hloc : Claim1411LocalR)
    (h152 : Item152R) (h153 : Item153MainR) (h155 : Item155wR) : Step1515HJD :=
  step1515HJD_of_res4 h134 h48 (step1515HJConj_of h152 h153 h155)
    (step1515HJQN_of h152 h153 h155) hloc

end HJ

end CFSG.RankThree.PartTwo.Sec15
