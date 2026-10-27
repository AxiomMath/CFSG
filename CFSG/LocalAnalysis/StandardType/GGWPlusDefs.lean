module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.StandardType

@[expose] def GGSolvQuotLeTwo {G : Type} [Group G] (X C : Subgroup G) : Prop :=
  ∀ (N : Subgroup X) [N.Normal], C.subgroupOf X ≤ N → IsSolvable (X ⧸ N) →
    Nat.card (X ⧸ N) ≤ 2

end CFSG.StandardType
