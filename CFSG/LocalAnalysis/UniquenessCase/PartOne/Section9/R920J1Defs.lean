module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs14
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R920J1 (D : Data G) : Prop :=
  ∀ L D₃ Y H : Subgroup G, PartTwo.Hyp919c D L D₃ Y H → Y ≤ L → IsJ1 (Bar2 Y) → False

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
