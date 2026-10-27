module

import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofFusion
import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofCent
import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofIndex
public import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17

theorem step163U35K_holds : Step163U35K :=
  step163U35K_of Res3U35.ks163U35NoIndex25 Res3U35.ks163U35CentA7 Res3U35.ks163U35Fusion

theorem step163U35_of_conj (hC : Step163U35Conj) : Step163U35 :=
  step163U35_of step163U35K_holds hC

end CFSG.RankThree.PartTwo.Sec16
