module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdLeafKProof
public import CFSG.RankThree.PartTwo.J2Residue.KFacts
import CFSG.RankThree.PartTwo.J2Residue.Beta

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

theorem step166KCommD_of_kfacts
    (h143 : Sec14.Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hG1 : J2Residue.KG1) (hfix : J2Residue.KJFix) (hsplit : J2Residue.KJSplit)
    (hcover : J2Residue.KJCover) : Step166KCommD :=
  step166KCommD_of_beta h143 h134 h48 h1514 hMeets
    (J2Residue.false_of_beta hG1 hfix hsplit hcover)

end CFSG.RankThree.PartTwo.Sec16.Kd166
