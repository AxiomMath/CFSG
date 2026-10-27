module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.SubgroupLists

theorem quad_eq_zero_of_pow_eq_one_of_sq {p : ℕ} [hp : Fact p.Prime] {n : Type} [Fintype n]
    [DecidableEq n] {x : Matrix n n (ZMod p)} {k : ℕ} (hk : x ^ k = 1) (hpk : ¬ p ∣ k)
    {τ : ZMod p} (hsq : (x * x - τ • x + 1) ^ 2 = 0) : x * x - τ • x + 1 = 0 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => hpk (h ▸ dvd_zero p)
  have hr : Nat.totient k ≠ 0 := (Nat.totient_pos.mpr hk0).ne'
  have hmod : p ^ Nat.totient k % k = 1 % k :=
    Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpk)
  have hx : x ^ p ^ Nat.totient k = x := by
    rw [pow_eq_pow_mod _ hk, hmod, ← pow_eq_pow_mod 1 hk, pow_one]
  have hc : Commute (x * x + 1) (τ • x) :=
    (((Commute.refl x).mul_left (Commute.refl x)).add_left (Commute.one_left x)).smul_right τ
  have hfrob : (x * x - τ • x + 1) ^ p ^ Nat.totient k = x * x - τ • x + 1 := by
    rw [sub_add_eq_add_sub, sub_pow_char_pow_of_commute p _ hc,
      add_pow_char_pow_of_commute p _ (Commute.one_right _), (Commute.refl x).mul_pow, one_pow,
      smul_pow, ZMod.pow_card_pow, hx]
  have h2le : 2 ≤ p ^ Nat.totient k := Nat.one_lt_pow hr hp.out.one_lt
  rw [← hfrob]
  exact pow_eq_zero_of_le h2le hsq

section Weight

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

private theorem cubic_mul_cubic {N : Matrix n n K} (hN : N ^ 4 = 0) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : K) :
    (a₀ • 1 + a₁ • N + a₂ • N ^ 2 + a₃ • N ^ 3) * (b₀ • 1 + b₁ • N + b₂ • N ^ 2 + b₃ • N ^ 3) =
      (a₀ * b₀) • 1 + (a₀ * b₁ + a₁ * b₀) • N + (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) • N ^ 2 +
        (a₀ * b₃ + a₁ * b₂ + a₂ * b₁ + a₃ * b₀) • N ^ 3 := by
  have h5 : N ^ 5 = 0 := by rw [pow_succ, hN, zero_mul]
  have h6 : N ^ 6 = 0 := by rw [pow_succ, h5, zero_mul]
  have e11 : N * N = N ^ 2 := (sq N).symm
  have e12 : N * N ^ 2 = N ^ 3 := (pow_succ' N 2).symm
  have e21 : N ^ 2 * N = N ^ 3 := (pow_succ N 2).symm
  have e13 : N * N ^ 3 = 0 := (pow_succ' N 3).symm.trans hN
  have e31 : N ^ 3 * N = 0 := (pow_succ N 3).symm.trans hN
  have e22 : N ^ 2 * N ^ 2 = 0 := (pow_add N 2 2).symm.trans hN
  have e23 : N ^ 2 * N ^ 3 = 0 := (pow_add N 2 3).symm.trans h5
  have e32 : N ^ 3 * N ^ 2 = 0 := (pow_add N 3 2).symm.trans h5
  have e33 : N ^ 3 * N ^ 3 = 0 := (pow_add N 3 3).symm.trans h6
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, e11, e12, e21, e13, e31,
    e22, e23, e32, e33, smul_zero, add_zero, zero_add]
  module

private theorem smul_mul_eq_of_quad {h X : Matrix n n K} {τ μ : K} (hq : h * h - τ • h + 1 = 0)
    (hX : h * X = μ • (X * h)) (hμ : μ ≠ 1) : (τ * μ) • (X * h) = (1 + μ) • X := by
  have hh : h * h = τ • h - 1 := by linear_combination (norm := module) hq
  have e1 : h * h * X = (τ * μ) • (X * h) - X := by
    rw [hh, sub_mul, smul_mul_assoc, hX, one_mul, smul_smul]
  have e2 : h * h * X = (μ * μ) • (τ • (X * h) - X) := by
    rw [Matrix.mul_assoc, hX, mul_smul_comm, ← Matrix.mul_assoc, hX, smul_mul_assoc, smul_smul,
      Matrix.mul_assoc, hh, Matrix.mul_sub, mul_smul_comm, Matrix.mul_one]
  have e3 : (1 - μ) • ((τ * μ) • (X * h) - (1 + μ) • X) = 0 := by
    linear_combination (norm := module) e1.symm.trans e2
  rcases smul_eq_zero.mp e3 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1).symm hμ
  · exact sub_eq_zero.mp h1

theorem sub_one_mul_self_eq_zero_of_conj_pow (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {g h : Matrix n n K} (hN : (g - 1) ^ 4 = 0) {m : ℕ} (hconj : h * g = g ^ m * h) {τ : K}
    (hq : h * h - τ • h + 1 = 0) (hm : (m : K) ^ 2 ≠ 1) : (g - 1) * (g - 1) = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N, g = 1 + N := ⟨g - 1, by abel⟩
  rw [add_sub_cancel_left] at hN ⊢
  have hm1 : (m : K) ≠ 1 := fun h1 => hm (by rw [h1, one_pow])
  have hmm : (m : K) * m ≠ 1 := fun h1 => hm (by rw [sq, h1])
  have hg : (1 : Matrix n n K) + N =
      (1 : K) • 1 + (1 : K) • N + (0 : K) • N ^ 2 + (0 : K) • N ^ 3 := by
    module
  have hpow : ∀ j : ℕ, ∃ a b : K,
      (1 + N) ^ j = (1 : K) • 1 + (j : K) • N + a • N ^ 2 + b • N ^ 3 ∧
        2 * a = j * (j - 1) ∧ 6 * b = j * (j - 1) * (j - 2) := by
    intro j
    induction j with
    | zero => exact ⟨0, 0, by simp, by simp, by simp⟩
    | succ j ih =>
      obtain ⟨a, b, hj, ha, hb⟩ := ih
      refine ⟨j + a, a + b, ?_, ?_, ?_⟩
      · rw [pow_succ, hj, hg, cubic_mul_cubic hN]
        push_cast
        module
      · push_cast
        linear_combination ha
      · push_cast
        linear_combination 3 * ha + hb
  obtain ⟨a, b, hgm, ha, hb⟩ := hpow m
  obtain ⟨M, hMdef⟩ : ∃ M, M = (1 + N) ^ m - 1 := ⟨_, rfl⟩
  have hM : M = (0 : K) • 1 + (m : K) • N + a • N ^ 2 + b • N ^ 3 := by
    rw [hMdef, hgm]
    module
  have hM2 : M ^ 2 =
      (0 : K) • 1 + (0 : K) • N + ((m : K) * m) • N ^ 2 + (2 * (m : K) * a) • N ^ 3 := by
    rw [sq, hM, cubic_mul_cubic hN]
    module
  have hM3 : M ^ 3 = (0 : K) • 1 + (0 : K) • N + (0 : K) • N ^ 2 + ((m : K) * m * m) • N ^ 3 := by
    rw [pow_succ, hM2, hM, cubic_mul_cubic hN]
    module
  have hN1 : h * N = M * h := by
    rw [hMdef, sub_mul, ← hconj, one_mul, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
  have hNj : ∀ j : ℕ, h * N ^ j = M ^ j * h := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
    | succ j ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hN1, ← Matrix.mul_assoc, ← pow_succ]
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Matrix n n K,
      Λ = (0 : K) • 1 + (6 : K) • N + (-3 : K) • N ^ 2 + (2 : K) • N ^ 3 := ⟨_, rfl⟩
  have hcomb : (0 : K) • (1 : Matrix n n K) + (6 : K) • M + (-3 : K) • M ^ 2 + (2 : K) • M ^ 3 =
      (m : K) • Λ := by
    have e2 : (6 : K) * a + -3 * ((m : K) * m) = -3 * m := by linear_combination 3 * ha
    have e3 : (6 : K) * b + -3 * (2 * m * a) + 2 * ((m : K) * m * m) = 2 * m := by
      linear_combination hb - 3 * m * ha
    calc _ = (0 : K) • (1 : Matrix n n K) + (6 * (m : K)) • N +
          ((6 : K) * a + -3 * ((m : K) * m)) • N ^ 2 +
          ((6 : K) * b + -3 * (2 * m * a) + 2 * ((m : K) * m * m)) • N ^ 3 := by
          rw [hM2, hM3, hM]
          module
      _ = (m : K) • Λ := by
          rw [e2, e3, hΛdef]
          module
  have hΛ : h * Λ = (m : K) • (Λ * h) := by
    have e : h * Λ = ((0 : K) • 1 + (6 : K) • M + (-3 : K) • M ^ 2 + (2 : K) • M ^ 3) * h := by
      rw [hΛdef]
      simp only [Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
        Matrix.one_mul, hN1, hNj 2, hNj 3]
    rw [e, hcomb, smul_mul_assoc]
  have hΛ2 : h * (Λ * Λ) = ((m : K) * m) • (Λ * Λ * h) := by
    rw [← Matrix.mul_assoc, hΛ, smul_mul_assoc, Matrix.mul_assoc, hΛ, mul_smul_comm, smul_smul,
      ← Matrix.mul_assoc]
  have E1 := smul_mul_eq_of_quad hq hΛ hm1
  have E2 := smul_mul_eq_of_quad hq hΛ2 hmm
  have E3 : (τ * ((m : K) * m)) • (Λ * Λ * h) = ((m : K) * (1 + m)) • (Λ * Λ) := by
    calc (τ * ((m : K) * m)) • (Λ * Λ * h) = (m : K) • (Λ * ((τ * m) • (Λ * h))) := by
          rw [mul_smul_comm, smul_smul, ← Matrix.mul_assoc]
          congr 1
          ring
      _ = (m : K) • (Λ * ((1 + (m : K)) • Λ)) := by rw [E1]
      _ = ((m : K) * (1 + m)) • (Λ * Λ) := by rw [mul_smul_comm, smul_smul]
  have E4 : (1 - (m : K)) • (Λ * Λ) = 0 := by
    linear_combination (norm := module) E3 - E2
  have hL2 : Λ * Λ = 0 := (smul_eq_zero.mp E4).resolve_left (sub_ne_zero.mpr (Ne.symm hm1))
  have hΛsq : Λ * Λ = (0 : K) • 1 + (0 : K) • N + (36 : K) • N ^ 2 + (-36 : K) • N ^ 3 := by
    rw [hΛdef, cubic_mul_cubic hN]
    module
  have hΛcube : Λ * Λ * Λ = (216 : K) • N ^ 3 := by
    rw [hΛsq, hΛdef, cubic_mul_cubic hN]
    module
  have h216 : (216 : K) ≠ 0 := by
    rw [show (216 : K) = 2 ^ 3 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have h36 : (36 : K) ≠ 0 := by
    rw [show (36 : K) = 2 ^ 2 * 3 ^ 2 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hN3 : N ^ 3 = 0 := by
    have e : (216 : K) • N ^ 3 = 0 := by rw [← hΛcube, hL2, Matrix.zero_mul]
    exact (smul_eq_zero.mp e).resolve_left h216
  have e : (36 : K) • N ^ 2 = 0 := by
    have e' := hΛsq
    rw [hL2, hN3] at e'
    linear_combination (norm := module) -e'
  rw [← sq]
  exact (smul_eq_zero.mp e).resolve_left h36

end Weight

end CFSG.RankThree.SubgroupLists
