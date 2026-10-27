module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

namespace s16h_SL4MixedAux1

@[expose] def s16h_SL4Mixed (V L : Subgroup G) (hV : IsElemAbelian 2 V) (x r : G) : Prop :=
  ¬ (barSub ⊥ V hV (Subgroup.zpowers r) ≤ barSub ⊥ V hV L) ∧
    ¬ (barSub ⊥ V hV (Subgroup.zpowers r) ≤
      barSub ⊥ V hV (conjSubgroup L x))

end s16h_SL4MixedAux1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
