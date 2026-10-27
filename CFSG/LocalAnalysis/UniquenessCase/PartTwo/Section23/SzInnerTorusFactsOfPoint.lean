module

public import CFSG.GroupTheory.SuzukiPointTorus.Basic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def SzPointActionFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), IsSz X f →
    CFSG.GroupTheory.SuzukiTorusData X (2 ^ f)

end CFSG.LocalAnalysis.UniquenessCase.UC22
