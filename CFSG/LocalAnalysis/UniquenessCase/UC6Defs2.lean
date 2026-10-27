module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C625 : Prop := CFSG.Open.pRank m.r m.K = 1

@[expose] def C634 : Prop := ¬ ∃ t ∈ m.K, ∀ z ∈ m.Z, t * z * t⁻¹ = z⁻¹

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
