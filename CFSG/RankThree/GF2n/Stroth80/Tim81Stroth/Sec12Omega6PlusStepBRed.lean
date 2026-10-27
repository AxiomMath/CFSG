module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec12Induction
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Sec12Omega6PlusQStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G)
    [(Q.subgroupOf M).Normal] [(Q.subgroupOf (H0 M Z)).Normal] (hc : Ctx M Q Z B) (n : ℕ),
    Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → OmegaPlusNat hc t 3 →
    SubConfigSatz M Q Z (hc.CN t) →
      Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) = Nat.card Z

end CFSG.RankThree.GF2n.Stroth80
