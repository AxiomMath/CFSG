module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem isPGroup_LB_of_ctx (hc : Ctx M Q Z B) : IsPGroup 2 ↥(LB M Q B) := by
  have hB : IsZConjugate Z B := hc.conj
  have hQB : IsPGroup 2 ↥(QB B) := hB.isPGroup_QB hc.hyp
  have hQBM : IsPGroup 2 ↥(QB B ⊓ M) := hQB.to_inf_left
  have hQ : IsPGroup 2 ↥Q := isPGroup_Q' hc.hyp
  have hnorm : (QB B ⊓ M) ≤ Subgroup.normalizer (Q : Set G) :=
    inf_le_right.trans hc.hyp.Q_normal.2
  change IsPGroup 2 ↥(Q ⊔ (QB B ⊓ M))
  exact IsPGroup.to_sup_of_normal_left' hQ hQBM hnorm

end CFSG.RankThree.GF2n.Stroth80
