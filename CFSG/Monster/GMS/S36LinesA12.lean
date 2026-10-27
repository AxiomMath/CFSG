module

public import CFSG.Monster.GMS.Graph
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Monster.GMS

open Equiv Equiv.Perm

private def swapsProd : List (Fin 12 × Fin 12) → Perm (Fin 12)
  | [] => 1
  | (p, q) :: l => swap p q * swapsProd l

private def DisjointSwaps : List (Fin 12 × Fin 12) → Prop
  | [] => True
  | (p, q) :: l => p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l

private instance (l : List (Fin 12 × Fin 12)) : Decidable (DisjointSwaps l) := by
  induction l with
  | nil => exact isTrue trivial
  | cons pq l ih =>
    obtain ⟨p, q⟩ := pq
    exact inferInstanceAs
      (Decidable (p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l))

namespace S36Lines

variable {G : Type*} [Group G] {a z₀ : G}

structure A12Fusion (a z₀ : G) (φ : alternatingGroup (Fin 12) →* G) : Prop where
  injective : Function.Injective φ
  comm : ∀ σ, φ σ * a = a * φ σ
  isConj_a : ∀ σ : alternatingGroup (Fin 12),
    ((σ : Perm (Fin 12)).cycleType = {2, 2} ∨ (σ : Perm (Fin 12)).cycleType = {2, 2, 2, 2, 2, 2}) →
      IsConj a (φ σ)
  isConj_z : ∀ σ : alternatingGroup (Fin 12),
    (σ : Perm (Fin 12)).cycleType = {2, 2, 2, 2} → IsConj z₀ (φ σ)

end S36Lines

@[expose] def A12FusionAt {G : Type*} [Group G] (a z₀ : G) : Prop :=
  ∃ φ : alternatingGroup (Fin 12) →* G, S36Lines.A12Fusion a z₀ φ

end CFSG.Monster.GMS
