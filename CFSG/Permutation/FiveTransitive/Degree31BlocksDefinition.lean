module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.Degree31Blocks

@[expose] def blocks {X : Type} (P : Subgroup (Equiv.Perm X)) : Set (Finset X) :=
  {b | b.card = 7 ∧ Nat.card (fixingSubgroup P (b : Set X)) = 2048}

@[expose] def blocksThrough {X : Type} (P : Subgroup (Equiv.Perm X)) (s : Set X) :=
  {b : Finset X // b ∈ blocks P ∧ s ⊆ (b : Set X)}

@[expose] noncomputable def blockFinset {X : Type} [Fintype X]
    (P : Subgroup (Equiv.Perm X)) : Finset (Finset X) :=
  (blocks P).toFinite.toFinset

@[simp] theorem mem_blockFinset {X : Type} [Fintype X]
    (P : Subgroup (Equiv.Perm X)) (b : Finset X) :
    b ∈ blockFinset P ↔ b ∈ blocks P := by
  classical
  exact Set.Finite.mem_toFinset _

end FiveTransitive.Degree31Blocks

end CFSG
