module

public import CFSG.LocalAnalysis.WeakClosure81.EightOne
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_26_NE (D : Data G) (V₀ V H₀ : Subgroup G) : Prop :=
  Hyp125 D V₀ V → Hyp124Min D H₀ → 4 < mSub V₀ → ¬ IsCalH0 V₀ H₀ →
    E1.InE D.k (H₀ ⊓ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
