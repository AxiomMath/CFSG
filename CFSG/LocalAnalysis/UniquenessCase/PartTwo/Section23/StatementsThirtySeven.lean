module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsUniqueN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_37_B2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ K ∈ calC D.M, (K.subgroupOf D.M).Normal →
    ∀ (m : ℕ) (A₀ : Subgroup G), IsInnerCartanOnL A₀ K c.L D.T m →
      ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m ∧ ⁅A, c.B0⁆ = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22
