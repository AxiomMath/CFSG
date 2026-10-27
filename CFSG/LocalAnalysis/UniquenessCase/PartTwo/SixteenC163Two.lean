module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_3_2 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L → IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 →
      Case163_2 D V₀ V hV L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
