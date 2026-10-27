module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_20b (D : Data G) : Prop :=
  ∀ V₀ V p L A t B r (h : Ctx19_10 D V₀ V p L A t B r), Even (S17.nOf L) →
    ∃ E : Subgroup G, E ≤ A ∧ E ≠ ⊥ ∧ ¬ 3 ∣ Nat.card E ∧ normalizer (E : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
