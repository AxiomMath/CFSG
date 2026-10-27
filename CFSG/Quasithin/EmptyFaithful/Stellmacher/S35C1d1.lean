module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open Equiv

section Perm3

@[expose] def cyc3 : Perm (Fin 3) := swap 0 1 * swap 1 2

variable {A : Type*} [CommGroup A]

theorem perm3_eq_cyc_pow_mul_swap (σ : Perm (Fin 3)) :
    ∃ i j : ℕ, σ = cyc3 ^ i * swap 0 1 ^ j := by
  have h : ∀ σ : Perm (Fin 3), ∃ i : Fin 3, ∃ j : Fin 2,
      σ = cyc3 ^ (i : ℕ) * swap 0 1 ^ (j : ℕ) := by
    unfold cyc3; decide +kernel
  obtain ⟨i, j, h⟩ := h σ
  exact ⟨i, j, h⟩

theorem act_pow_fix (ρ : Perm (Fin 3) →* MulAut A) {σ : Perm (Fin 3)} {w : A} (h : ρ σ w = w)
    (n : ℕ) : ρ (σ ^ n) w = w := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, map_mul, MulAut.mul_apply, h, ih]

theorem act_fix_all (ρ : Perm (Fin 3) →* MulAut A) {w : A} (hc : ρ cyc3 w = w)
    (ht : ρ (swap 0 1) w = w) (σ : Perm (Fin 3)) : ρ σ w = w := by
  obtain ⟨i, j, rfl⟩ := perm3_eq_cyc_pow_mul_swap σ
  rw [map_mul, MulAut.mul_apply, act_pow_fix ρ ht, act_pow_fix ρ hc]

theorem act_mul_apply (ρ : Perm (Fin 3) →* MulAut A) (σ τ : Perm (Fin 3)) (w : A) :
    ρ (σ * τ) w = ρ σ (ρ τ w) := by
  rw [map_mul, MulAut.mul_apply]

theorem cyc3_fix_eq_one (ρ : Perm (Fin 3) →* MulAut A) (hA : ∀ x : A, x * x = 1)
    (hfix : ∀ w : A, (∀ σ, ρ σ w = w) → w = 1) {w : A} (hw : ρ cyc3 w = w) : w = 1 := by
  have h1 : ρ (swap 0 1) (ρ (swap 0 1) w) = w := by
    rw [← act_mul_apply]
    have : swap (0 : Fin 3) 1 * swap 0 1 = 1 := by decide
    rw [this, map_one]; rfl
  have h2 : ρ cyc3 (ρ (swap 0 1) w) = ρ (swap 0 1) w := by
    rw [← act_mul_apply]
    have : cyc3 * swap (0 : Fin 3) 1 = swap 0 1 * (cyc3 * cyc3) := by unfold cyc3; decide
    rw [this, act_mul_apply, act_mul_apply, hw, hw]
  have hw' : w * ρ (swap 0 1) w = 1 := by
    refine hfix _ (act_fix_all ρ ?_ ?_)
    · rw [map_mul, hw, h2]
    · rw [map_mul, h1, mul_comm]
  have hinv : ρ (swap 0 1) w = w := by
    have : ρ (swap 0 1) w = w⁻¹ := eq_inv_of_mul_eq_one_right hw'
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (hA w)).symm
  exact hfix _ (act_fix_all ρ hw hinv)

theorem cyc3_norm (ρ : Perm (Fin 3) →* MulAut A) (hA : ∀ x : A, x * x = 1)
    (hfix : ∀ w : A, (∀ σ, ρ σ w = w) → w = 1) (z : A) :
    z * ρ cyc3 z * ρ (cyc3 * cyc3) z = 1 := by
  refine cyc3_fix_eq_one ρ hA hfix ?_
  have e : cyc3 * (cyc3 * cyc3) = 1 := by unfold cyc3; decide
  have h3 : ρ cyc3 (ρ (cyc3 * cyc3) z) = z := by
    rw [← act_mul_apply, e, map_one]; rfl
  rw [map_mul, map_mul, h3, ← act_mul_apply ρ cyc3 cyc3 z]
  ac_rfl

theorem eq_prod_transpositions (ρ : Perm (Fin 3) →* MulAut A) (hA : ∀ x : A, x * x = 1)
    (hfix : ∀ w : A, (∀ σ, ρ σ w = w) → w = 1) (y : A) :
    y = (y * ρ (swap 0 1) y) * (y * ρ (swap 1 2) y) * (y * ρ (swap 0 2) y) := by
  set z := ρ (swap 0 1) y with hz
  have hy : y = ρ (swap 0 1) z := by
    rw [hz, ← act_mul_apply]
    have : swap (0 : Fin 3) 1 * swap 0 1 = 1 := by decide
    rw [this, map_one]; rfl
  have e1 : ρ (swap 1 2) y = ρ (cyc3 * cyc3) z := by
    rw [hy, ← act_mul_apply]
    have : swap (1 : Fin 3) 2 * swap 0 1 = cyc3 * cyc3 := by unfold cyc3; decide
    rw [this]
  have e2 : ρ (swap 0 2) y = ρ cyc3 z := by
    rw [hy, ← act_mul_apply]
    have : swap (0 : Fin 3) 2 * swap 0 1 = cyc3 := by unfold cyc3; decide
    rw [this]
  have hn := cyc3_norm ρ hA hfix z
  have key : (y * z) * (y * ρ (cyc3 * cyc3) z) * (y * ρ cyc3 z) =
      (y * y * y) * (z * ρ cyc3 z * ρ (cyc3 * cyc3) z) := by ac_rfl
  rw [e1, e2, key, hn, mul_one, hA, one_mul]
