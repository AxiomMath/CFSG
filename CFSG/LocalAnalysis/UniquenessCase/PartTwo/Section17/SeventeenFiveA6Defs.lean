module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def ExpFourAut17 (D : Data G) (L : Subgroup G) : Prop :=
  ∀ t ∈ NTL17 D L, t ^ 4 ∈ centSection (L ⊔ D.T) L (CFSG.Open.pCoreOf 2 L)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
