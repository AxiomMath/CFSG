module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_38_perf (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ X : Subgroup G, X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) →
    c.B0 ≤ Subgroup.normalizer (X : Set G) →
    (∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) →
    X ≤ CFSG.Open.pCoreOf 2 D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
