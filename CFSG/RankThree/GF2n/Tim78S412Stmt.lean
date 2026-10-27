module

public import CFSG.RankThree.GF2n.Tim78S4Setting

public section

namespace CFSG.RankThree.GF2n.Tim78

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Step412 (M B P Q : Subgroup G) : Prop :=
  ¬ ∃ x ∈ classD B, x ∈ M ∧ x ∉ Q ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ B

end CFSG.RankThree.GF2n.Tim78
