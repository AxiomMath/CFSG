module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.A5Fin

open Equiv

set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 1000000

theorem exists_inverted_three : ∀ σ k : Perm (Fin 5), Perm.sign σ = -1 → σ * σ = 1 →
    Perm.sign k = 1 → k * k = 1 → k ≠ 1 → σ * k = k * σ →
    ∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y * y * y = 1 ∧ y ≠ 1 ∧ σ * y = y * σ ∧
      k * y * k⁻¹ = y⁻¹ := by
  decide +kernel

theorem exists_prod_five : ∀ k : Perm (Fin 5), Perm.sign k = 1 → k * k = 1 → k ≠ 1 →
    ∃ h : Perm (Fin 5), Perm.sign h = 1 ∧ (k * (h * k * h⁻¹)) ^ 5 = 1 ∧
      k * (h * k * h⁻¹) ≠ 1 := by
  decide +kernel

def a₁ : Perm (Fin 5) := swap 0 1 * swap 2 3

def a₃ : Perm (Fin 5) := swap 0 1 * swap 1 2

def a₂ : Perm (Fin 5) := a₃ * a₁ * a₃⁻¹

theorem kleinData : a₁ * a₁ = 1 ∧ a₂ * a₂ = 1 ∧ a₁ * a₂ = a₂ * a₁ ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
    a₁ ≠ a₂ ∧ a₃ * a₁ * a₃⁻¹ = a₂ ∧ a₃ * a₂ * a₃⁻¹ = a₁ * a₂ ∧ Perm.sign a₁ = 1 ∧
    Perm.sign a₂ = 1 ∧ Perm.sign a₃ = 1 ∧ a₁ 4 = 4 ∧ a₂ 4 = 4 ∧ a₃ 4 = 4 := by
  unfold a₁ a₂ a₃
  decide +kernel

end CFSG.Quasithin.A5Fin
