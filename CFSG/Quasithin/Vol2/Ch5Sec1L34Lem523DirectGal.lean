module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.Quasithin.H13.Direct523Gal

open Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_pow_two_pow (σ : K ≃+* K) : ∃ i : ℕ, ∀ x : K, σ x = x ^ (2 ^ i) := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let σa : K ≃ₐ[ZMod 2] K :=
    { σ with
      commutes' := fun r => by
        have h := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K))
          (algebraMap (ZMod 2) K)
        exact congrArg (fun f => f r) h }
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K σa
  refine ⟨i, fun x => ?_⟩
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  have := hi x
  rw [h2] at this
  exact this

theorem pow_natCard (x : K) : x ^ Nat.card K = x := by
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem not_forall_pow {m : ℕ} (hm : 2 ≤ m) (hK : m < Nat.card K) :
    ¬ ∀ x : K, x ^ m = x := by
  intro h
  have hdeg : (X ^ m - X : K[X]).natDegree = m := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow m
    · rw [natDegree_X_pow, natDegree_X]; omega
  have hzero : (X ^ m - X : K[X]) = 0 := by
    apply Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    · intro r
      simp [h r]
    · rw [hdeg, ← Nat.cast_card]
      exact_mod_cast hK
  have hcoeff : (X ^ m - X : K[X]).coeff 1 = 0 := by rw [hzero]; simp
  have hm1 : m ≠ 1 := by omega
  rw [coeff_sub, coeff_X_pow, coeff_X, if_neg (Ne.symm hm1)] at hcoeff
  simp at hcoeff

theorem pow_pow_card_pow {a : ℕ} (hK : Nat.card K = 2 ^ a) (q : ℕ) (x : K) :
    x ^ ((2 ^ a) ^ q) = x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, pow_mul, ih]
    rw [← hK]
    exact pow_natCard x

theorem dvd_of_pow_two_pow_fixed {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ a) {k : ℕ}
    (h : ∀ x : K, x ^ (2 ^ k) = x) : a ∣ k := by
  by_contra hna
  have hr : 0 < k % a := Nat.pos_of_ne_zero (fun h0 => hna (Nat.dvd_of_mod_eq_zero h0))
  have hr_lt : k % a < a := Nat.mod_lt _ (by omega)
  have key : ∀ q r : ℕ, k = a * q + r → ∀ x : K, x ^ (2 ^ r) = x := by
    intro q r hkqr x
    have h1 := h x
    have e : x ^ (2 ^ (a * q + r)) = (x ^ ((2 ^ a) ^ q)) ^ (2 ^ r) := by
      rw [pow_add, pow_mul 2 a q, pow_mul x]
    rw [hkqr, e, pow_pow_card_pow hK] at h1
    exact h1
  have hfix : ∀ x : K, x ^ (2 ^ (k % a)) = x := key (k / a) (k % a) (Nat.div_add_mod k a).symm
  have hm2 : 2 ≤ 2 ^ (k % a) := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k % a) := Nat.pow_le_pow_right (by norm_num) hr
  have hmK : 2 ^ (k % a) < Nat.card K := by
    rw [hK]; exact Nat.pow_lt_pow_right (by norm_num) hr_lt
  exact not_forall_pow hm2 hmK hfix

theorem pow_four_pow {μ : K} (h : μ ^ 4 = μ) (j : ℕ) : μ ^ (4 ^ j) = μ := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, ih, h]

theorem fix_F4_of_sq (hK : Nat.card K = 16) (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x) :
    ∀ μ : K, μ ^ 4 = μ → σ μ = μ := by
  obtain ⟨i, hi⟩ := exists_pow_two_pow σ
  have hK' : Nat.card K = 2 ^ 4 := by rw [hK]; norm_num
  have e : (2 : ℕ) ^ i * 2 ^ i = 2 ^ (2 * i) := by
    rw [← pow_add]; congr 1; ring
  have h2 : ∀ x : K, x ^ (2 ^ (2 * i)) = x := by
    intro x
    have := hσ x
    rw [hi, hi, ← pow_mul, e] at this
    exact this
  obtain ⟨j, hj⟩ : ∃ j, i = 2 * j := by
    have hd := dvd_of_pow_two_pow_fixed (by norm_num) hK' h2
    exact ⟨i / 2, by omega⟩
  intro μ hμ
  rw [hi, hj]
  have e2 : (2 : ℕ) ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
  rw [e2]
  exact pow_four_pow hμ j

theorem eq_id_of_pow_three {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ a)
    (hco : Nat.Coprime 3 a) (σ : K ≃+* K) (h3 : ∀ x, σ (σ (σ x)) = x) : ∀ x, σ x = x := by
  obtain ⟨i, hi⟩ := exists_pow_two_pow σ
  have e3 : (2 : ℕ) ^ i * (2 ^ i * 2 ^ i) = 2 ^ (3 * i) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have h3' : ∀ x : K, x ^ (2 ^ (3 * i)) = x := by
    intro x
    have := h3 x
    rw [hi, hi, hi, ← pow_mul, ← pow_mul, e3] at this
    exact this
  have hd := dvd_of_pow_two_pow_fixed ha hK h3'
  have hdi : a ∣ i := (Nat.Coprime.dvd_mul_left hco.symm).mp hd
  obtain ⟨j, rfl⟩ := hdi
  intro x
  rw [hi, pow_mul 2 a j]
  exact pow_pow_card_pow hK j x

end CFSG.Quasithin.H13.Direct523Gal
