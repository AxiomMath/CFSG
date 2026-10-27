module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

@[expose] def C625 : Prop := CFSG.Open.pRank m.r m.K = 1

@[expose] def C634 : Prop := ¬ ∃ t ∈ m.K, ∀ z ∈ m.Z, t * z * t⁻¹ = z⁻¹

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
