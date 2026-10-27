module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121B
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121TB
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem s21_21TB_of_s21_21B {D : Data G} {Ch : Choice2011 G} (h : S21_21B D Ch) :
    S21_21TB D Ch := by
  intro h1930 c hB hH p hp
  obtain ⟨hinf, -, n, hsh, hpow, hpn, hr⟩ := h h1930 c hB hH p hp
  exact ⟨hinf, n, hsh.imp And.left And.left, hpow, hpn, hr⟩

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
