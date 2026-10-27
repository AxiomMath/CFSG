module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm

public section

open Equiv

namespace A7T3

@[expose] def ga : Perm (Fin 7) := swap 0 3 * swap 0 2 * swap 0 1 * swap 4 5

@[expose] def gb : Perm (Fin 7) := swap 0 2 * swap 4 5

@[expose] def T0l : List (Perm (Fin 7)) :=
  [1, ga, swap 0 2 * swap 1 3, swap 0 1 * swap 0 2 * swap 0 3 * swap 4 5, gb, swap 0 3 * swap 1 2,
    swap 1 3 * swap 4 5, swap 0 1 * swap 2 3]

@[expose] def permT0 (σ : Perm (Fin 7)) : Prop :=
  ∀ t ∈ T0l, ∃ j : Fin 3, ∃ t' ∈ T0l, t * σ = σ ^ (j : ℕ) * t'

instance (σ : Perm (Fin 7)) : Decidable (permT0 σ) := by unfold permT0; infer_instance

@[expose] def cond (σ : Perm (Fin 7)) : Prop :=
  Perm.sign σ = 1 → σ ^ 9 = 1 → σ ^ 3 = 1 ∧ (permT0 σ → ∃ t ∈ T0l, t * σ * t⁻¹ = σ⁻¹)

instance (σ : Perm (Fin 7)) : Decidable (cond σ) := by unfold cond; infer_instance

@[expose] def mulT0 : Prop := ∀ a ∈ T0l, ∀ b ∈ T0l, a * b ∈ T0l

instance : Decidable mulT0 := by unfold mulT0; infer_instance

@[expose] def invT0 : Prop := ∀ a ∈ T0l, a⁻¹ ∈ T0l

instance : Decidable invT0 := by unfold invT0; infer_instance

@[expose] def evenT0 : Prop := ∀ a ∈ T0l, Perm.sign a = 1

instance : Decidable evenT0 := by unfold evenT0; infer_instance

@[expose] def allCond : Prop := ∀ σ : Perm (Fin 7), cond σ

instance : Decidable allCond := by unfold allCond; infer_instance

@[expose] def stmt : Prop := mulT0 ∧ invT0 ∧ T0l.Nodup ∧ evenT0 ∧ allCond

instance : Decidable stmt := by unfold stmt; infer_instance

@[expose] def a7Check : Bool := decide stmt

end A7T3
