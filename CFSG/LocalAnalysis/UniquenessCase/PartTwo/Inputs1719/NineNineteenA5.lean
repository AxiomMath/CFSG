module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R9_19A5 (D : Data G) : Prop :=
  IsStronglyPEmbedded 5 D.M →
    ∀ (L D₃ Y H : Subgroup G), PartTwo.Hyp919c D L D₃ Y H → IsAlt (Bar2 L) 5 → L ≤ Y →
      pCoreOf 2 Y ≠ ⊥ → rankThreeIsMaxTwoLocal H → Y ∈ calY2_9 D

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
