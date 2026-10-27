module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResClose
import CFSG.RankThree.PartTwo.J2Residue.KG1Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem step152SL25OneOmegaResR_of_j2
    (hfix : J2Residue.KJFix) (hsplit : J2Residue.KJSplit) (hcover : J2Residue.KJCover)
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne) :
    Step152SL25OneOmegaResR :=
  step152SL25OneOmegaResR_of J2Residue.kg1_holds hfix hsplit hcover h142 h134 h48 hcomp

theorem step152SL25OneOmegaR_of_j2
    (hfix : J2Residue.KJFix) (hsplit : J2Residue.KJSplit) (hcover : J2Residue.KJCover)
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne)
    (hlist : Step1515HJListLe) (h155 : Item155wJ2R) : Step152SL25OneOmegaR :=
  step152SL25OneOmegaR_of_res h142 h134 h48 hcomp hlist h155
    (step152SL25OneOmegaResR_of_j2 hfix hsplit hcover h142 h134 h48 hcomp)

end CFSG.RankThree.PartTwo.Sec15
