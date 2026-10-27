module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IrrOn)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C621 : Prop := IrrOn (m.L ⊓ normalizer (m.A : Set G)) (m.A ⊓ m.L)

@[expose] def C621x : Prop :=
  ∃ x ∈ normalizer (m.A : Set G), x ^ 4 ∈ centralizer (m.A : Set G) ∧
    ∀ a ∈ m.A, (x ^ 2 * a * (x ^ 2)⁻¹ = a ↔ a ∈ m.Z)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
