module

public import CFSG.RankThree.PartOne.A6N.Defs

public section

namespace CFSG.RankThree.PartOne.A6N

open Equiv

@[expose] def g₂ : Perm (Fin 6) := swap 0 1 * swap 1 3

@[expose] def t₂ : Perm (Fin 6) := swap 0 5 * swap 5 1 * swap 2 3 * swap 3 4

@[expose] def k₀ : Perm (Fin 6) := swap 1 3 * swap 4 5

theorem g₂_mem : g₂ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem t₂_mem : t₂ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem k₀_mem : k₀ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

@[expose] def g₂A : alternatingGroup (Fin 6) := ⟨g₂, g₂_mem⟩

@[expose] def t₂A : alternatingGroup (Fin 6) := ⟨t₂, t₂_mem⟩

@[expose] def k₀A : alternatingGroup (Fin 6) := ⟨k₀, k₀_mem⟩

@[simp] theorem coe_g₂A : (g₂A : Perm (Fin 6)) = g₂ := rfl

@[simp] theorem coe_t₂A : (t₂A : Perm (Fin 6)) = t₂ := rfl

@[simp] theorem coe_k₀A : (k₀A : Perm (Fin 6)) = k₀ := rfl

theorem y₀_g₂_comm : y₀ * g₂ = g₂ * y₀ := by decide

theorem y₀_pow_three : y₀ ^ 3 = 1 := by decide

theorem g₂_pow_three : g₂ ^ 3 = 1 := by decide

theorem k₀_y₀ : k₀ * y₀ * k₀⁻¹ = y₀⁻¹ := by decide +kernel

theorem k₀_g₂ : k₀ * g₂ * k₀⁻¹ = g₂⁻¹ := by decide +kernel

theorem g₂_word : g₂ = a₀ * a₀ * y₀ * y₀ * s₀ * a₀ * y₀ * s₀ * a₀ := by decide +kernel

theorem t₂_word : t₂ = a₀ * a₀ * y₁ * y₁ * s₀ * a₀ * y₁ * s₀ * a₀ := by decide +kernel

theorem y₀_g₂_indep : ∀ i j : Fin 3, y₀ ^ (i : ℕ) * g₂ ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
  decide +kernel

theorem y₀_g₂_inj : ∀ p q : Fin 3 × Fin 3,
    y₀ ^ (p.1 : ℕ) * g₂ ^ (p.2 : ℕ) = y₀ ^ (q.1 : ℕ) * g₂ ^ (q.2 : ℕ) → p = q := by
  decide +kernel

end CFSG.RankThree.PartOne.A6N
