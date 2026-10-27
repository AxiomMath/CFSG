module

public import CFSG.Monster.GMS.Graph
public import CFSG.Monster.GMS.S347

public section

namespace CFSG.Monster.GMS

section Defs

variable {G G' : Type*} [Group G] [Group G']

structure IsIsoOn (f : G → G') (H : Subgroup G) (H' : Subgroup G') : Prop where
  map_mem : ∀ x ∈ H, f x ∈ H'
  map_mul : ∀ x ∈ H, ∀ y ∈ H, f (x * y) = f x * f y
  injOn : Set.InjOn f H
  surjOn : ∀ y ∈ H', ∃ x ∈ H, f x = y

end Defs

section Graph

variable {G : Type*} [Group G]

@[expose] def LinesHaveInvolutions (a : G) : Prop :=
  ∀ x y z : G, IsConj a x → IsConj a y → z ∈ twoANbr a y →
    ∃ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {z}, orderOf t = 2

@[expose] def oddTypeStab : Fin 3 → ℕ
  | 0 => 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23
  | 1 => 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31
  | 2 => 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19

@[expose] def OddTypeOrders (a z₀ : G) : Prop :=
  ∀ x y : G, ∀ k : Fin 3, IsConj a x → y ∈ oddNbr a z₀ x → OddNbrType z₀ x y k →
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) = oddTypeStab k

end Graph

end CFSG.Monster.GMS
