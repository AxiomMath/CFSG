module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofU4Outer
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofSp4BT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof

theorem ks224Sp4 : KS224Sp4 :=
  ks224Sp4_of_borelTits ks224Sp4BorelTits

theorem ks224U4 : KS224U4 :=
  ks224U4_of ks224U4BorelTits ks224U4OutTwoCyclic

theorem ks224U5 : KS224U5 :=
  ks224U5_of ks224U5BorelTits ks224U5OutTwoCyclic

end CFSG.RankThree.PartTwo.Sec21
