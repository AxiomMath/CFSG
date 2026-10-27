module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Monster.Schur

@[expose] def NoPerfectTripleCover (G : Type*) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → Group.IsPerfect E →
    Nat.card π.ker ≠ 3

end CFSG.Monster.Schur
