module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.H13

open scoped Pointwise

@[expose] def WielandtCoprimeProduct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G), Group.IsNilpotent ↥A →
    Group.IsNilpotent ↥B → Nat.Coprime (Nat.card A) (Nat.card B) →
    (A : Set G) * (B : Set G) = Set.univ → Group.IsSolvable G

end CFSG.Quasithin.H13
