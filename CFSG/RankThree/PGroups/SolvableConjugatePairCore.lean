module

public import CFSG.GroupTheory.BaerConjugatePairPCore

public section

namespace CFSG.RankThree.PGroups

open Subgroup

variable {G : Type*} [Group G]

theorem solvable_conjugate_pair_core [Finite G] [Group.IsSolvable G] {p : ℕ} (hp : p.Prime)
    {a : G} (_ha : ∃ k : ℕ, orderOf a = p ^ k)
    (hpair : ∀ g : G, IsPGroup p (closure ({a, g⁻¹ * a * g} : Set G))) : a ∈ pCore p G :=
  have : Fact p.Prime := ⟨hp⟩
  (GroupTheory.baer_conjugate_pair_p_core (G := G) p).2 a hpair

end CFSG.RankThree.PGroups
