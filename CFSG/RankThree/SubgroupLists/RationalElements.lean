module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K]

theorem cayley_hamilton_three {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    A * A * A - A.trace • (A * A) + (adjugate A).trace • A -
      A.det • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three] <;> ring

theorem trace_mul_self_three {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    (A * A).trace = A.trace ^ 2 - 2 * (adjugate A).trace := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three]
  ring

theorem adjugate_eq_inv_of_det_eq_one (x : GL (Fin 3) K)
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    adjugate (x : Matrix (Fin 3) (Fin 3) K) =
      ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]

theorem trace_eq_of_isConj {n : ℕ} {x y : GL (Fin n) K} (h : IsConj x y) :
    (x : Matrix (Fin n) (Fin n) K).trace = (y : Matrix (Fin n) (Fin n) K).trace := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem isConj_pow {G : Type*} [Group G] {x y : G} (h : IsConj x y) (k : ℕ) :
    IsConj (x ^ k) (y ^ k) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [← hc, conj_pow]

theorem one_add_pow_of_cube_eq_zero {R : Type*} [Ring R] {N : R} (hN : N ^ 3 = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N + (n.choose 2) • N ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hN3 : N ^ 2 * N = 0 := by rw [← pow_succ]; exact hN
    rw [pow_succ, ih, mul_add, mul_one, add_mul, add_mul, one_mul, smul_mul_assoc,
      smul_mul_assoc, hN3, smul_zero, add_zero, ← sq, Nat.choose_succ_succ, Nat.choose_one_right,
      add_smul, add_smul, one_smul]
    abel

theorem eq_one_of_unipotent_of_pow_eq_one {x : Matrix (Fin 3) (Fin 3) K}
    (hN : (x - 1) ^ 3 = 0) {n : ℕ} (hn : (n : K) ≠ 0) (hxn : x ^ n = 1) : x = 1 := by
  set N := x - 1 with hNdef
  have hx : x = 1 + N := by rw [hNdef]; abel
  rw [hx, one_add_pow_of_cube_eq_zero hN] at hxn
  have h1 : n • N + (n.choose 2) • N ^ 2 = 0 := by
    have := congrArg (· - 1) hxn
    simp only [sub_self] at this
    rw [← this]
    abel
  have hsmul : ∀ M : Matrix (Fin 3) (Fin 3) K, n • M = 0 → M = 0 := by
    intro M hM
    rw [← Nat.cast_smul_eq_nsmul K] at hM
    exact (smul_eq_zero.mp hM).resolve_left hn
  have hN2 : N ^ 2 = 0 := by
    have h2 := congrArg (· * N) h1
    simp only [add_mul, zero_mul, smul_mul_assoc, ← pow_succ, hN, smul_zero, add_zero] at h2
    exact hsmul _ (by rw [sq]; exact h2)
  have hN1 : N = 0 := by
    rw [hN2, smul_zero, add_zero] at h1
    exact hsmul _ h1
  rw [hx, hN1, add_zero]

theorem cayley_hamilton_sl3 (x : GL (Fin 3) K) (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    (x : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (x : Matrix (Fin 3) (Fin 3) K).trace • (x : Matrix (Fin 3) (Fin 3) K) ^ 2 -
        ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace • (x : Matrix (Fin 3) (Fin 3) K) +
          1 := by
  have h := cayley_hamilton_three (x : Matrix (Fin 3) (Fin 3) K)
  rw [adjugate_eq_inv_of_det_eq_one x hdet, hdet, one_smul] at h
  rw [pow_succ, pow_two, ← sub_eq_zero, ← h]
  abel

theorem trace_sq_sl3 (x : GL (Fin 3) K) (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ((x : Matrix (Fin 3) (Fin 3) K) ^ 2).trace =
      (x : Matrix (Fin 3) (Fin 3) K).trace ^ 2 -
        2 * ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
  rw [pow_two, trace_mul_self_three, adjugate_eq_inv_of_det_eq_one x hdet]

theorem trace_cube_sl3 (x : GL (Fin 3) K) (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ((x : Matrix (Fin 3) (Fin 3) K) ^ 3).trace =
      (x : Matrix (Fin 3) (Fin 3) K).trace * ((x : Matrix (Fin 3) (Fin 3) K) ^ 2).trace -
        ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace *
          (x : Matrix (Fin 3) (Fin 3) K).trace + 3 := by
  rw [cayley_hamilton_sl3 x hdet, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  norm_num

theorem unipotent_of_trace_eq_three (x : GL (Fin 3) K)
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hτ : (x : Matrix (Fin 3) (Fin 3) K).trace = 3)
    (hσ : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 3) :
    ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 := by
  have h := cayley_hamilton_sl3 x hdet
  rw [hτ, hσ] at h
  set X := (x : Matrix (Fin 3) (Fin 3) K)
  have e : (X - 1) ^ 3 = X ^ 3 - (3 : K) • X ^ 2 + (3 : K) • X - 1 := by
    rw [ofNat_smul_eq_nsmul (R := K) (n := 3), ofNat_smul_eq_nsmul (R := K) (n := 3)]
    noncomm_ring
  rw [e, h]
  abel

theorem coe_pow_trace (x : GL (Fin 3) K) (k : ℕ) :
    ((x ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      ((x : Matrix (Fin 3) (Fin 3) K) ^ k).trace := by
  rw [Units.val_pow_eq_pow_val]

theorem trace_inv_eq_trace_pow (x : GL (Fin 3) K) {n : ℕ} (hxn : x ^ (n + 1) = 1) :
    ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      ((x : Matrix (Fin 3) (Fin 3) K) ^ n).trace := by
  have : x⁻¹ = x ^ n := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hxn]
  rw [this, coe_pow_trace]

theorem five_eq_zero_of_isConj_sq {x : GL (Fin 3) K}
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hconj : IsConj x (x ^ 2)) : (5 : K) = 0 := by
  by_contra h5
  set X := (x : Matrix (Fin 3) (Fin 3) K) with hX
  have h12 : X.trace = (X ^ 2).trace := by rw [← coe_pow_trace]; exact trace_eq_of_isConj hconj
  have h24 : (X ^ 2).trace = (X ^ 4).trace := by
    have := trace_eq_of_isConj (isConj_pow hconj 2)
    rw [coe_pow_trace, ← pow_mul, coe_pow_trace] at this
    exact this
  have hσ : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = X.trace := by
    rw [trace_inv_eq_trace_pow x hx5, ← h24, ← h12]
  have hτ : X.trace * (X.trace - 3) = 0 := by
    have := trace_sq_sl3 x hdet
    rw [hσ, ← h12] at this
    linear_combination -this
  rcases mul_eq_zero.mp hτ with h0 | h3
  ·
    have hc := cayley_hamilton_sl3 x hdet
    rw [hσ, h0, zero_smul, zero_smul, sub_zero, zero_add] at hc
    have hx3 : x ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_one])
    apply hx1
    calc x = x ^ 6 * (x ^ 5)⁻¹ := by group
      _ = 1 := by rw [show x ^ 6 = (x ^ 3) ^ 2 by group, hx3, hx5]; group
  ·
    have hτ3 : X.trace = 3 := by linear_combination h3
    have hN := unipotent_of_trace_eq_three x hdet hτ3 (by rw [hσ, hτ3])
    apply hx1
    apply Units.ext
    exact eq_one_of_unipotent_of_pow_eq_one (n := 5) hN (by exact_mod_cast h5)
      (by rw [← Units.val_pow_eq_pow_val, hx5, Units.val_one])

theorem sq_two_mul_trace_sub_one_eq_five {x : GL (Fin 3) K}
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1)
    (h5 : (5 : K) ≠ 0) (hconj : IsConj x (x ^ 4)) :
    (2 * (x : Matrix (Fin 3) (Fin 3) K).trace - 1) ^ 2 = 5 := by
  have hσ : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      (x : Matrix (Fin 3) (Fin 3) K).trace := by
    rw [trace_inv_eq_trace_pow x hx5, ← coe_pow_trace]
    exact (trace_eq_of_isConj hconj).symm
  have h23 : ((x : Matrix (Fin 3) (Fin 3) K) ^ 2).trace =
      ((x : Matrix (Fin 3) (Fin 3) K) ^ 3).trace := by
    have := trace_eq_of_isConj (isConj_pow hconj 2)
    rw [coe_pow_trace, ← pow_mul, show 4 * 2 = 5 + 3 by norm_num, pow_add, hx5, one_mul,
      coe_pow_trace] at this
    exact this
  have hsq := trace_sq_sl3 x hdet
  have hcu := trace_cube_sl3 x hdet
  rw [hσ] at hsq hcu
  rw [← h23, hsq] at hcu
  have hN : (x : Matrix (Fin 3) (Fin 3) K).trace = 3 →
      ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 := fun hτ3 =>
    unipotent_of_trace_eq_three x hdet hτ3 (by rw [hσ, hτ3])
  generalize (x : Matrix (Fin 3) (Fin 3) K).trace = τ at hcu hN ⊢
  have hpoly : (τ - 3) * (τ ^ 2 - τ - 1) = 0 := by
    linear_combination -hcu
  rcases mul_eq_zero.mp hpoly with h3 | h1
  · exfalso
    apply hx1
    apply Units.ext
    exact eq_one_of_unipotent_of_pow_eq_one (n := 5) (hN (by linear_combination h3))
      (by exact_mod_cast h5) (by rw [← Units.val_pow_eq_pow_val, hx5, Units.val_one])
  · linear_combination 4 * h1

theorem sq_two_mul_trace_add_one_eq_neg_seven {x : GL (Fin 3) K}
    (hdet : (x : Matrix (Fin 3) (Fin 3) K).det = 1) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1)
    (h2 : (2 : K) ≠ 0) (h7 : (7 : K) ≠ 0) (hconj : IsConj x (x ^ 2)) :
    (2 * (x : Matrix (Fin 3) (Fin 3) K).trace + 1) ^ 2 = -7 := by
  have h12 : (x : Matrix (Fin 3) (Fin 3) K).trace = ((x : Matrix (Fin 3) (Fin 3) K) ^ 2).trace := by
    rw [← coe_pow_trace]; exact trace_eq_of_isConj hconj
  have h36 : ((x : Matrix (Fin 3) (Fin 3) K) ^ 3).trace =
      ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
    have := trace_eq_of_isConj (isConj_pow hconj 3)
    rw [coe_pow_trace, ← pow_mul, coe_pow_trace] at this
    rw [this, trace_inv_eq_trace_pow x hx7]
  have hsq := trace_sq_sl3 x hdet
  have hcu := trace_cube_sl3 x hdet
  rw [← h12] at hsq hcu
  rw [h36] at hcu
  have hN : (x : Matrix (Fin 3) (Fin 3) K).trace = 3 →
      ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 3 →
      ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 :=
    unipotent_of_trace_eq_three x hdet
  generalize (x : Matrix (Fin 3) (Fin 3) K).trace = τ at hsq hcu hN ⊢
  generalize ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = σ at hsq hcu hN
  have hpoly : (τ - 3) * (τ ^ 2 + τ + 2) = 0 := by
    linear_combination -(τ + 1) * hsq + 2 * hcu
  rcases mul_eq_zero.mp hpoly with h3 | h1
  · exfalso
    have hτ3 : τ = 3 := by linear_combination h3
    have hσ3 : σ = 3 := by
      have : (2 : K) * (σ - 3) = 0 := by rw [hτ3] at hsq; linear_combination hsq
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    apply hx1
    apply Units.ext
    exact eq_one_of_unipotent_of_pow_eq_one (n := 7) (hN hτ3 hσ3) (by exact_mod_cast h7)
      (by rw [← Units.val_pow_eq_pow_val, hx7, Units.val_one])
  · linear_combination 4 * h1

end CFSG.RankThree.SubgroupLists
