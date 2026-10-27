module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest4
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21c
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

structure Steps78 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest : S21_3Rest4 D Ch
  s21_14 : S21_14 D Ch
  s21_12a : S21_12aF D Ch

end CFSG.LocalAnalysis.UniquenessCase.UC22
