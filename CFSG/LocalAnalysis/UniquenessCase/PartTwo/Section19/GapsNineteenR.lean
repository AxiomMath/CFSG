module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_18_5 (D : Data G) : Prop :=
  ∀ V₀ V p L A t B r Y N Dsub H S (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
    A ≤ normalizer (Dsub : Set G) → P19_16_5 D Dsub →
    ∃ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinComponentFamily D Dsub d K J ∧
      (¬ ⁅Opp 2 (Dsub ⊓ D.M), A⁆ ≤ pCoreOf 2 (Opp 2 (Dsub ⊓ D.M)) →
        ∃ i : Fin d, J i ≤ ⁅Opp 2 (Dsub ⊓ D.M), A⁆)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
