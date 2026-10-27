module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_17_elt (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx2311 D Ch, ∀ d ∈ c.L, Odd (orderOf d) → d ^ 3 ≠ 1 →
    (∀ k ∈ c.K, d * k * d⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.K) →
      (c.E ⊔ c.S) ⊓ Subgroup.centralizer ({d} : Set G) = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22
