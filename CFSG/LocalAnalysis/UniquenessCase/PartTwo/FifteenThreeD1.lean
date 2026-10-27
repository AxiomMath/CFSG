module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Core

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

@[expose] def R127One (D : Data G) : Prop :=
  (∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) →
    ∀ V : Subgroup G, InCalV D.M V → CFSG.CGT.Timmesfeld75.IsTI V → 8 ≤ Nat.card V →
      ¬ UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G))

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
