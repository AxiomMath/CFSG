module

public import CFSG.LinearAlgebra.SL2CoprimeOrder
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.Quasithin.SqModel

open scoped Matrix

variable {F : Type} [Field F]

theorem trace_eq_zero_of_commute_sq_zero [CharP F 2] (B N : Matrix (Fin 2) (Fin 2) F)
    (hN2 : N * N = 0) (hN : N ≠ 0) (hBN : B * N = N * B) : B.trace = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have e : ∀ i j : Fin 2, (N * N) i j = 0 := fun i j => by rw [hN2]; rfl
  have c : ∀ i j : Fin 2, (B * N) i j = (N * B) i j := fun i j => by rw [hBN]
  have e00 := e 0 0
  have e11 := e 1 1
  have c01 := c 0 1
  have c10 := c 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 c01 c10
  have hps : N 0 0 = N 1 1 := by
    have h3 : (N 0 0 - N 1 1) ^ 2 = 0 := by
      linear_combination e00 + e11 - (N 0 1 * N 1 0 + N 0 0 * N 1 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  have hq : (B 0 0 - B 1 1) * N 0 1 = 0 := by linear_combination c01 + B 0 1 * hps
  have hr : (B 0 0 - B 1 1) * N 1 0 = 0 := by linear_combination (-1 : F) * c10 + B 1 0 * hps
  have hxw : B 0 0 - B 1 1 = 0 := by
    by_contra hne
    have hq0 : N 0 1 = 0 := (mul_eq_zero.mp hq).resolve_left hne
    have hr0 : N 1 0 = 0 := (mul_eq_zero.mp hr).resolve_left hne
    apply hN
    have hp : N 0 0 = 0 := by
      have : N 0 0 * N 0 0 = 0 := by
        rw [hq0, hr0] at e00
        linear_combination e00
      exact mul_self_eq_zero.mp this
    have hs : N 1 1 = 0 := hps.symm.trans hp
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq0, hr0, hs]
  rw [Matrix.trace_fin_two]
  linear_combination hxw + B 1 1 * h2

theorem mul_self_eq_one_of_commute_involution [CharP F 2] (B u : Matrix (Fin 2) (Fin 2) F)
    (hdet : B.det = 1) (hu : u * u = 1) (hu1 : u ≠ 1) (hBu : B * u = u * B) : B * B = 1 := by
  have hN2 : (u - 1) * (u - 1) = 0 := by
    have h1 : (u - 1) * (u - 1) = u * u - (u + u) + 1 := by noncomm_ring
    rw [h1, hu, CharTwo.add_self_eq_zero u, sub_zero]
    exact CharTwo.add_self_eq_zero 1
  have hBN : B * (u - 1) = (u - 1) * B := by rw [mul_sub, sub_mul, hBu, mul_one, one_mul]
  have ht := trace_eq_zero_of_commute_sq_zero B (u - 1) hN2 (sub_ne_zero.mpr hu1) hBN
  rw [CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one B hdet, ht, zero_smul, zero_sub]
  exact CharTwo.neg_eq 1

theorem trace_pow_two_pow_eq [CharP F 2] (n : ℕ) (B : Matrix (Fin 2) (Fin 2) F)
    (hdet : B.det = 1) (h : B * B = 1 ∨ B ^ 2 ^ n = B ∨ B ^ 2 ^ n * B = 1) :
    B.trace ^ 2 ^ n = B.trace := by
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp at hdet
  have hCH : B * B = B.trace • B - 1 := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one B hdet
  have hCH' : B * B + B.trace • B + 1 = 0 := by
    rw [hCH]
    have : B.trace • B - 1 + B.trace • B + 1 = B.trace • B + B.trace • B := by abel
    rw [this, CharTwo.add_self_eq_zero]
  have hq0 : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have key : B * B + B.trace ^ 2 ^ n • B + 1 = 0 →
      B.trace ^ 2 ^ n = B.trace := by
    intro hk
    have hsub : (B.trace ^ 2 ^ n - B.trace) • B = 0 := by
      rw [sub_smul]
      have : B * B + B.trace ^ 2 ^ n • B + 1 - (B * B + B.trace • B + 1) =
          B.trace ^ 2 ^ n • B - B.trace • B := by abel
      rw [← this, hk, hCH', sub_zero]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hB0
  have hpow : (B * B + B.trace • B + 1) ^ 2 ^ n =
      (B ^ 2 ^ n) * (B ^ 2 ^ n) + B.trace ^ 2 ^ n • B ^ 2 ^ n + 1 := by
    have hc1 : Commute (B * B) (B.trace • B) :=
      ((Commute.refl B).mul_left (Commute.refl B)).smul_right _
    have hc2 : Commute (B * B + B.trace • B) 1 := Commute.one_right _
    rw [add_pow_char_pow_of_commute 2 n hc2, add_pow_char_pow_of_commute 2 n hc1, one_pow,
      (Commute.refl B).mul_pow, smul_pow]
  rw [hCH', zero_pow hq0] at hpow
  rcases h with h | h | h
  ·
    have h1 : B.trace • B = 0 := by
      have : B.trace • B - 1 = 1 := by rw [← hCH, h]
      rw [eq_add_of_sub_eq this, CharTwo.add_self_eq_zero]
    have : B.trace = 0 := (smul_eq_zero.mp h1).resolve_right hB0
    rw [this, zero_pow hq0]
  ·
    rw [h] at hpow
    exact key hpow.symm
  ·
    have hBP : B * B ^ 2 ^ n = 1 := (((Commute.refl B).pow_left (2 ^ n)).eq).symm.trans h
    have h1 : B * B * (B ^ 2 ^ n * B ^ 2 ^ n) = 1 := by
      calc B * B * (B ^ 2 ^ n * B ^ 2 ^ n) = B * (B * B ^ 2 ^ n) * B ^ 2 ^ n := by
            simp only [mul_assoc]
        _ = 1 := by rw [hBP, mul_one, hBP]
    have h2 : B * B * B ^ 2 ^ n = B := by
      rw [mul_assoc, hBP, mul_one]
    have h3 := congrArg (fun X => B * B * X) hpow.symm
    simp only [mul_add, mul_zero, Matrix.mul_smul, h1, h2, mul_one] at h3
    apply key
    have h4 : B * B + B.trace ^ 2 ^ n • B + 1 = 1 + B.trace ^ 2 ^ n • B + B * B := by abel
    rw [h4]
    exact h3

theorem trace_pow_eq_of_mem_closure [CharP F 2] (n : ℕ) {S : Set (Matrix (Fin 2) (Fin 2) F)}
    (hS : ∀ A ∈ S, A.trace ^ 2 ^ n = A.trace) :
    ∀ A ∈ AddSubgroup.closure S, A.trace ^ 2 ^ n = A.trace := by
  intro A hA
  induction hA using AddSubgroup.closure_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.trace_add, add_pow_char_pow, hx, hy]
  | neg x _ hx => rw [Matrix.trace_neg, CharTwo.neg_eq, hx]

theorem card_le_of_pow_eq_self [Fintype F] {q : ℕ} (hq : 1 < q) (h : ∀ f : F, f ^ q = f) :
    Fintype.card F ≤ q := by
  classical
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial F).natDegree = q :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ q - Polynomial.X : Polynomial F).roots := by
    intro f _
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, h f]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rwa [hdeg, Finset.card_univ] at this

end CFSG.Quasithin.SqModel
