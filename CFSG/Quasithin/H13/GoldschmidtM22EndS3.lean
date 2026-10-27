module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.GM22

open Equiv

theorem perm3_centralizer_swap :
    ∀ τ σ : Perm (Fin 3), τ.support.card = 2 → σ * τ = τ * σ → σ = 1 ∨ σ = τ := by
  decide +kernel

theorem perm3_exists_noncomm :
    ∀ τ : Perm (Fin 3), τ.support.card = 2 → ∃ ρ : Perm (Fin 3), ρ * τ ≠ τ * ρ := by
  decide +kernel

theorem perm3_coset_cover :
    ∀ τ ρ κ : Perm (Fin 3), τ.support.card = 2 → ρ * τ ≠ τ * ρ →
      κ * τ = τ * κ ∨ (κ * ρ⁻¹) * τ = τ * (κ * ρ⁻¹) ∨
        (κ * (ρ * τ)⁻¹) * τ = τ * (κ * (ρ * τ)⁻¹) := by
  decide +kernel

theorem perm3_noncomm_conj :
    ∀ τ σ : Perm (Fin 3), τ.support.card = 2 → σ * τ ≠ τ * σ →
      (σ⁻¹ * τ * σ) * τ ≠ τ * (σ⁻¹ * τ * σ) ∧ (σ * τ * σ⁻¹) * τ ≠ τ * (σ * τ * σ⁻¹) := by
  decide +kernel

theorem perm3_prod_order :
    ∀ τ σ : Perm (Fin 3), τ.support.card = 2 → σ * τ ≠ τ * σ →
      (τ * (σ⁻¹ * τ * σ)) ^ 3 = 1 ∧ τ * (σ⁻¹ * τ * σ) ≠ 1 := by
  decide +kernel

theorem perm3_center_trivial :
    ∀ s : Perm (Fin 3), (∀ t : Perm (Fin 3), t * s = s * t) → s = 1 := by
  decide +kernel

theorem perm3_normal_two :
    ∀ s : Perm (Fin 3), (∀ κ : Perm (Fin 3), (s * (κ * s * κ⁻¹)) ^ 2 = 1) → s = 1 := by
  decide +kernel

theorem perm3_swap_sq : ∀ τ : Perm (Fin 3), τ.support.card = 2 → τ ^ 2 = 1 := by
  decide +kernel

theorem perm3_gen_conj :
    ∀ τ σ κ : Perm (Fin 3), τ.support.card = 2 → σ * τ ≠ τ * σ →
      κ = 1 ∨ κ = τ ∨ κ = σ⁻¹ * τ * σ ∨ κ = τ * (σ⁻¹ * τ * σ) ∨ κ = (σ⁻¹ * τ * σ) * τ ∨
        κ = τ * (σ⁻¹ * τ * σ) * τ := by
  decide +kernel

theorem perm3_sq_of_pow_two_pow (w : Perm (Fin 3)) (m : ℕ) (hw : w ^ 2 ^ m = 1) : w ^ 2 = 1 := by
  have h3 : ∀ s : Perm (Fin 3), s ^ 3 = 1 ∨ s ^ 2 = 1 := by decide +kernel
  rcases h3 w with h | h
  · have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h, hw⟩
    rw [hcop.gcd_eq_one, pow_one] at this
    rw [this, one_pow]
  · exact h

end CFSG.Quasithin.H13.GM22
