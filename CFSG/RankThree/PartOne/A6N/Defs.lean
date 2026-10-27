module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartOne.A6N

open Equiv

@[expose] def a₀ : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def s₀ : Perm (Fin 6) := swap 1 4 * swap 2 3

@[expose] def y₀ : Perm (Fin 6) := swap 2 4 * swap 4 5

@[expose] def y₁ : Perm (Fin 6) := swap 0 5 * swap 5 1 * swap 2 4 * swap 4 3

theorem a₀_mem : a₀ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem s₀_mem : s₀ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem y₀_mem : y₀ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem y₁_mem : y₁ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

@[expose] def a₀A : alternatingGroup (Fin 6) := ⟨a₀, a₀_mem⟩

@[expose] def s₀A : alternatingGroup (Fin 6) := ⟨s₀, s₀_mem⟩

@[expose] def y₀A : alternatingGroup (Fin 6) := ⟨y₀, y₀_mem⟩

@[expose] def y₁A : alternatingGroup (Fin 6) := ⟨y₁, y₁_mem⟩

@[simp] theorem coe_a₀A : (a₀A : Perm (Fin 6)) = a₀ := rfl

@[simp] theorem coe_s₀A : (s₀A : Perm (Fin 6)) = s₀ := rfl

@[simp] theorem coe_y₀A : (y₀A : Perm (Fin 6)) = y₀ := rfl

@[simp] theorem coe_y₁A : (y₁A : Perm (Fin 6)) = y₁ := rfl

theorem y₀_ne_y₁ : y₀ ≠ y₁ := by decide +kernel

theorem a₀_pow_five : a₀ ^ 5 = 1 := by decide

theorem a₀_ne_one : a₀ ≠ 1 := by decide

theorem s₀_mul_self : s₀ * s₀ = 1 := by decide

theorem s₀_mul_a₀ : s₀ * a₀ * s₀⁻¹ = a₀⁻¹ := by decide

end CFSG.RankThree.PartOne.A6N
