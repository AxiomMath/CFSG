module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofSigma
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofSigma
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14


theorem step158InnerRank_of_route (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R) :
    Step158InnerRank :=
  step158InnerRank_of_kfacts h134 h48 h148 kl3SigmaAutE9 ks158CentSolvR

theorem item158Y0R_of_cartanP
    (h131 : Item131) (h138 : Item138N) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) (hC : Step158CartanP) : Item158Y0R :=
  item158Y0R_of_kfacts h131 h138 h134 h48 h148 kl3SigmaAutE9 ks158CentSolvR hC

end CFSG.RankThree.PartTwo.Sec15
