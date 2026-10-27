module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResRoute
import CFSG.RankThree.PartTwo.J2Residue.KJFixHolds
import CFSG.RankThree.PartTwo.J2Residue.KJSplitH2
import CFSG.RankThree.PartTwo.J2Residue.KJCoverHolds

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem step152SL25OneOmegaR_of_items
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hcomp : Step143HJCompOne) (hlist : Step1515HJListLe) (h155 : Item155wJ2R) :
    Step152SL25OneOmegaR :=
  step152SL25OneOmegaR_of_j2 J2Residue.kJFix_holds J2Residue.kJSplit_holds
    J2Residue.kJCover_holds h142 h134 h48 hcomp hlist h155

end CFSG.RankThree.PartTwo.Sec15
