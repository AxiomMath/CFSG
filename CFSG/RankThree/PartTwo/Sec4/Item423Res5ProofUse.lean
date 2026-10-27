module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5Proof
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3Proof423
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofJ3
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofLTypeThree
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofCover
public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaJ4

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item4_23_of_res5
    (h45 : Item4_5) (h46 : Item4_6) (hCov : K423CoverFrame) (h3 : K423Inner46Three)
    (hθ : K423SporThetaCent) (h6 : K423Inner46SixLieRest) (hθ7 : K423ThetaCentSeven)
    (h8 : K423Inner46EightRest) : Item4_23 :=
  item4_23_of_res2W h45 h46 (k423SLThree_of_typeC h45 k423TypeCAlpha_holds k423TypeCAlphaSL_holds)
      (k423Cover_of h45 h46 hCov) h3 hθ k423SporJ3
      (k423SporJ4_of CFSG.AGLEmbeddingD2.Wilson.Coordinator.k423J4ThetaCentral) k423SporMcL
      (k423Inner46SixRest_of (k423Inner46SixLie_of h6)) hθ7 k423SevenSp62 h8

end CFSG.RankThree.PartTwo.Sec4
