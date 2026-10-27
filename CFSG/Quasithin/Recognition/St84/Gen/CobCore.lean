module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public section

namespace CFSG.Quasithin.St84

open Finset

variable {K : Type*} [Field K] {n : ℕ}

private lemma coeff_eq_of_bilin_expansion [Fintype K] [CharP K 2] {n : ℕ}
    (hlt : 2 ^ (n - 1) < Fintype.card K) {a b : Fin n → Fin n → K}
    (h : ∀ x y : K, (∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) =
      ∑ i, ∑ j, b i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) : a = b := by
  have hz : ∀ x y : K,
      (∑ i, ∑ j, (a i j - b i j) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) = 0 := by
    intro x y
    calc
      ∑ i, ∑ j, (a i j - b i j) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))
          = (∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) -
            ∑ i, ∑ j, b i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
            simp only [sub_mul, Finset.sum_sub_distrib]
      _ = 0 := by rw [h x y, sub_self]
  have hzero := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero
    (p := 2) hlt (a := fun i j => a i j - b i j) hz
  funext i j
  exact sub_eq_zero.mp (congrFun (congrFun hzero i) j)

private lemma coeff_eq_of_linearized_expansion [Fintype K] [CharP K 2] {n : ℕ}
    (hlt : 2 ^ (n - 1) < Fintype.card K) {a b : Fin n → K}
    (h : ∀ x : K, (∑ i, a i * x ^ 2 ^ (i : ℕ)) = ∑ i, b i * x ^ 2 ^ (i : ℕ)) : a = b := by
  have hz : ∀ x : K, (∑ i, (a i - b i) * x ^ 2 ^ (i : ℕ)) = 0 := by
    intro x
    calc
      ∑ i, (a i - b i) * x ^ 2 ^ (i : ℕ)
          = (∑ i, a i * x ^ 2 ^ (i : ℕ)) - ∑ i, b i * x ^ 2 ^ (i : ℕ) := by
            simp only [sub_mul, Finset.sum_sub_distrib]
      _ = 0 := by rw [h x, sub_self]
  have hzero := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_mul_pow_eq_zero
    (p := 2) hlt (a := fun i => a i - b i) hz
  funext i
  exact sub_eq_zero.mp (congrFun hzero i)

private lemma mul_sum_frob_expand [NeZero n] (d : Fin n → K) (x y : K) :
    y * (∑ k : Fin n, d k * x ^ 2 ^ (k : ℕ)) =
      ∑ i : Fin n, ∑ j : Fin n,
        (if j = 0 then d i else 0) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
  have hR : (∑ i : Fin n, ∑ j : Fin n,
      (if j = 0 then d i else 0) * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ))) =
      ∑ i : Fin n, d i * (x ^ 2 ^ (i : ℕ) * y) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (0 : Fin n)]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


private def eta (Φ : K → K → K) (p t : K) : K :=
  Φ p t + t * Φ p 1

private lemma eta_add_right {Φ : K → K → K}
    (hadd : ∀ p s t : K, Φ p (s + t) = Φ p s + Φ p t) (p s t : K) :
    eta Φ p (s + t) = eta Φ p s + eta Φ p t := by
  simp only [eta, hadd p s t]
  ring

private lemma eta_add_left [CharP K 2] {Φ : K → K → K}
    (hmod : ∀ p p' : K, ∃ w : K, ∀ t : K, Φ (p + p') t = Φ p t + Φ p' t + t * w)
    (p p' t : K) : eta Φ (p + p') t = eta Φ p t + eta Φ p' t := by
  obtain ⟨w, hw⟩ := hmod p p'
  have h1 := hw t
  have h2 := hw 1
  simp only [eta, h1, h2, one_mul]
  linear_combination (t * w) * (CharTwo.two_eq_zero : (2 : K) = 0)

private lemma eta_one [CharP K 2] {Φ : K → K → K} (p : K) : eta Φ p 1 = 0 := by
  simp only [eta, one_mul]
  exact CharTwo.add_self_eq_zero (Φ p 1)

private lemma eta_torus [CharP K 2] {Φ : K → K → K}
    (htor : ∀ c : K, c ≠ 0 → ∀ p : K, ∃ w : K, ∀ t : K,
      Φ (c * p) (c ^ 2 * t) = c * Φ p t + t * w)
    {c : K} (hc : c ≠ 0) (p t : K) :
    eta Φ (c * p) (c ^ 2 * t) = c * eta Φ p t + c ^ 3 * t * eta Φ p (c⁻¹ ^ 2) := by
  obtain ⟨w, hw⟩ := htor c hc p
  have h1 := hw t
  have h2 := hw (c⁻¹ ^ 2)
  have hc2 : c ^ 2 * (c⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  rw [hc2] at h2
  have e2 : (c ^ 2 * t) * ((c⁻¹) ^ 2 * w) = t * w := by
    rw [show (c ^ 2 * t) * ((c⁻¹) ^ 2 * w) = (c ^ 2 * (c⁻¹) ^ 2) * (t * w) by ring,
      hc2, one_mul]
  have e3 : c ^ 3 * (c⁻¹) ^ 2 = c := by
    rw [show c ^ 3 * (c⁻¹) ^ 2 = c * (c ^ 2 * (c⁻¹) ^ 2) by ring, hc2, mul_one]
  simp only [eta, h1, h2]
  rw [mul_add, mul_add, mul_add, e2]
  rw [show c ^ 3 * t * ((c⁻¹) ^ 2 * Φ p 1) = (c ^ 3 * (c⁻¹) ^ 2) * (t * Φ p 1) by ring, e3]
  linear_combination (t * w - c * t * Φ p 1) *
    (CharTwo.two_eq_zero : (2 : K) = 0)

private lemma eta_at_one {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s : K) : eta Φ 1 s = ∑ j, (∑ i, a i j) * s ^ 2 ^ (j : ℕ) := by
  rw [ha 1 s]
  simp only [one_pow, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

private lemma eta_swap_expand {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s t : K) : eta Φ t s = ∑ i, ∑ j, a j i * (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [ha t s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma scale_frob_monomial (c p t : K) (i j : ℕ) :
    (c * p) ^ 2 ^ i * (c ^ 2 * t) ^ 2 ^ j =
      c ^ (2 ^ i + 2 ^ (j + 1)) * (p ^ 2 ^ i * t ^ 2 ^ j) := by
  have hB : (c ^ 2 * t) ^ 2 ^ j = c ^ 2 ^ (j + 1) * t ^ 2 ^ j := by
    rw [mul_pow, ← pow_mul, show 2 * 2 ^ j = 2 ^ (j + 1) by rw [pow_succ']]
  calc
    (c * p) ^ 2 ^ i * (c ^ 2 * t) ^ 2 ^ j
        = (c ^ 2 ^ i * p ^ 2 ^ i) * (c ^ 2 ^ (j + 1) * t ^ 2 ^ j) := by
          rw [hB, mul_pow]
    _ = (c ^ 2 ^ i * c ^ 2 ^ (j + 1)) * (p ^ 2 ^ i * t ^ 2 ^ j) := by ring
    _ = c ^ (2 ^ i + 2 ^ (j + 1)) * (p ^ 2 ^ i * t ^ 2 ^ j) := by rw [← pow_add]

private lemma eta_scale_expand {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (c p t : K) :
    eta Φ (c * p) (c ^ 2 * t) =
      ∑ i, ∑ j, (a i j * c ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1))) *
        (p ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [ha (c * p) (c ^ 2 * t)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [scale_frob_monomial]
  ring

private lemma eta_linear_expand {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (c p t : K) :
    c * eta Φ p t =
      ∑ i, ∑ j, (c * a i j) * (p ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [ha p t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma mul_eta_const_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (p C t : K) :
    t * eta Φ p C =
      ∑ i : Fin n, ∑ j : Fin n,
        (if j = 0 then ∑ k : Fin n, a i k * C ^ 2 ^ (k : ℕ) else 0) *
        (p ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  have hC : eta Φ p C =
      ∑ i : Fin n, (∑ k : Fin n, a i k * C ^ 2 ^ (k : ℕ)) * p ^ 2 ^ (i : ℕ) := by
    rw [ha p C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hC]
  exact mul_sum_frob_expand (d := fun i : Fin n => ∑ k : Fin n, a i k * C ^ 2 ^ (k : ℕ))
    (x := p) (y := t)

private lemma mul_eta_one_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s t : K) :
    t * eta Φ 1 s =
      ∑ i : Fin n, ∑ j : Fin n,
        (if j = 0 then ∑ l : Fin n, a l i else 0) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [eta_at_one ha s]
  exact mul_sum_frob_expand (d := fun i : Fin n => ∑ l : Fin n, a l i) (x := s) (y := t)

private lemma mul_eta_one_swap [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s t : K) :
    s * eta Φ 1 t =
      ∑ i : Fin n, ∑ j : Fin n,
        (if i = 0 then ∑ l : Fin n, a l j else 0) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [eta_at_one ha t]
  rw [mul_sum_frob_expand (d := fun j : Fin n => ∑ l : Fin n, a l j) (x := t) (y := s)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma eta_symm_lhs_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s t : K) :
    eta Φ s t + t * eta Φ 1 s =
      ∑ i : Fin n, ∑ j : Fin n,
        (a i j + (if j = 0 then ∑ l : Fin n, a l i else 0)) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [ha s t, mul_eta_one_expand ha s t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma eta_symm_rhs_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (s t : K) :
    eta Φ t s + s * eta Φ 1 t =
      ∑ i : Fin n, ∑ j : Fin n,
        (a j i + (if i = 0 then ∑ l : Fin n, a l j else 0)) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [eta_swap_expand ha s t, mul_eta_one_swap ha s t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma two_pow_add_eq_two_pow {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : 2 ^ a + 2 ^ b = 2 ^ n) : a = n - 1 ∧ b = n - 1 := by
  have h1 : 2 ^ a ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 ^ (n - 1) + 2 ^ (n - 1) = 2 * 2 ^ (n - 1) := by rw [two_mul]
      _ = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
      _ = 2 ^ n := by rw [show (n - 1) + 1 = n by omega]
  have ha' : 2 ^ a = 2 ^ (n - 1) := by
    by_contra hne
    have hlt : 2 ^ a < 2 ^ (n - 1) := lt_of_le_of_ne h1 hne
    omega
  have hb' : 2 ^ b = 2 ^ (n - 1) := by
    by_contra hne
    have hlt : 2 ^ b < 2 ^ (n - 1) := lt_of_le_of_ne h2 hne
    omega
  exact ⟨Nat.pow_right_injective (by norm_num) ha', Nat.pow_right_injective (by norm_num) hb'⟩

private lemma not_dvd_two_pow_add_sub_one {n i j : ℕ} (hn : 2 ≤ n) (hi : i < n) (hj : 1 ≤ j)
    (hjn : j < n) (hne : (i, j) ≠ (n - 1, n - 2)) :
    ¬ (2 ^ n - 1) ∣ 2 ^ i + 2 ^ (j + 1) - 1 := by
  intro hdvd
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hEpos : 0 < 2 ^ i + 2 ^ (j + 1) - 1 := by
    have h1 : 0 < 2 ^ i := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    have h2 : 0 < 2 ^ (j + 1) := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    omega
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hjn) with hlt | heq
  · have hEq : 2 ^ i + 2 ^ (j + 1) - 1 = 2 ^ n - 1 := by
      have hle := Nat.le_of_dvd hEpos hdvd
      have hile : i ≤ n - 1 := by omega
      have hjle : j + 1 ≤ n - 1 := by omega
      have h1 : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hile
      have h2 : 2 ^ (j + 1) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hjle
      have h3 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        calc
          2 ^ (n - 1) + 2 ^ (n - 1) = 2 * 2 ^ (n - 1) := by rw [two_mul]
          _ = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
          _ = 2 ^ n := by rw [show (n - 1) + 1 = n by omega]
      omega
    have hsum : 2 ^ i + 2 ^ (j + 1) = 2 ^ n := by omega
    obtain ⟨hi', hj'⟩ := two_pow_add_eq_two_pow hi hlt hsum
    have hj2 : j + 1 = n - 1 := by simpa [Nat.succ_eq_add_one] using hj'
    have hjeq : j = n - 2 := by omega
    exact hne (Prod.ext hi' hjeq)
  · have hdvd2 : 2 ^ n - 1 ∣ 2 ^ i := by
      have h' : 2 ^ n - 1 ∣ 2 ^ i + (2 ^ n - 1) := by
        have e : 2 ^ i + 2 ^ (j + 1) - 1 = 2 ^ i + (2 ^ n - 1) := by
          rw [show j + 1 = n by omega]
          exact Nat.add_sub_assoc (Nat.one_le_two_pow : 1 ≤ 2 ^ n) (2 ^ i)
        rwa [e] at hdvd
      exact (Nat.dvd_add_iff_left (dvd_refl (2 ^ n - 1))).mpr h'
    have hlt : 2 ^ i < 2 ^ n - 1 := by
      have hile : i ≤ n - 1 := by omega
      have h1 : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hile
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        calc
          2 ^ n = 2 ^ ((n - 1) + 1) := by rw [show (n - 1) + 1 = n by omega]
          _ = 2 * 2 ^ (n - 1) := by rw [pow_succ']
      have hc : 2 ≤ 2 ^ (n - 1) := by
        have : 1 ≤ n - 1 := by omega
        simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) this
      omega
    have := Nat.le_of_dvd (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)) hdvd2
    omega

private lemma inv_sq_pow (c : K) (k : ℕ) :
    (c⁻¹ ^ 2) ^ 2 ^ k = (c⁻¹) ^ 2 ^ (k + 1) := by
  rw [← pow_mul, pow_succ']

private lemma eta_cob_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (c p t : K) :
    c ^ 3 * t * eta Φ p (c⁻¹ ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        (if j = 0 then ∑ k : Fin n, c ^ 3 * a i k * (c⁻¹) ^ 2 ^ ((k : ℕ) + 1) else 0) *
        (p ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  have hmul : c ^ 3 * t * eta Φ p (c⁻¹ ^ 2) = c ^ 3 * (t * eta Φ p (c⁻¹ ^ 2)) := by
    ring
  rw [hmul, mul_eta_const_expand ha p (c⁻¹ ^ 2) t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = 0
  · simp only [hj, if_true]
    rw [← mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inv_sq_pow]
    ring
  · simp [hj]

private lemma eta_torus_rhs_expand [NeZero n] {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (c p t : K) :
    c * eta Φ p t + c ^ 3 * t * eta Φ p (c⁻¹ ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        (c * a i j +
          (if j = 0 then ∑ k : Fin n, c ^ 3 * a i k * (c⁻¹) ^ 2 ^ ((k : ℕ) + 1) else 0)) *
        (p ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ)) := by
  rw [eta_linear_expand ha c p t, eta_cob_expand ha c p t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma coeff_torus_family [Fintype K] [CharP K 2] [NeZero n]
    (hlt : 2 ^ (n - 1) < Fintype.card K) {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (htor : ∀ c : K, c ≠ 0 → ∀ p t : K,
      eta Φ (c * p) (c ^ 2 * t) = c * eta Φ p t + c ^ 3 * t * eta Φ p (c⁻¹ ^ 2))
    {c : K} (hc : c ≠ 0) :
    (fun i j => a i j * c ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1))) =
      fun i j => c * a i j +
        (if j = 0 then ∑ k : Fin n, c ^ 3 * a i k * (c⁻¹) ^ 2 ^ ((k : ℕ) + 1) else 0) := by
  refine coeff_eq_of_bilin_expansion hlt ?_
  intro p t
  rw [← eta_scale_expand ha c p t, ← eta_torus_rhs_expand ha c p t]
  exact htor c hc p t

private lemma dvd_of_coeff_torus [Fintype K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {a : Fin n → Fin n → K} {i j : Fin n}
    (hij : a i j ≠ 0)
    (hcoef : ∀ c : K, c ≠ 0 →
      a i j * c ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1)) = c * a i j) :
    2 ^ n - 1 ∣ 2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1) - 1 := by
  classical
  have hEpos : 0 < 2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1) := by
    have h1 : 0 < 2 ^ (i : ℕ) := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    have h2 : 0 < 2 ^ ((j : ℕ) + 1) := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    omega
  have hforall : ∀ u : Kˣ, u ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1) - 1) = 1 := by
    intro u
    have hu : (u : K) ≠ 0 := u.ne_zero
    have h := hcoef (u : K) hu
    have h' : (u : K) ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1)) = (u : K) := by
      apply mul_left_cancel₀ hij
      rw [h, mul_comm]
    have hU : u ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1)) = u := Units.ext (by simpa using h')
    have hstep : u ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1) - 1) * u = 1 * u := by
      rw [← pow_succ, Nat.sub_add_cancel hEpos, hU, one_mul]
    exact mul_right_cancel hstep
  have hexp : Monoid.exponent Kˣ ∣ 2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1) - 1 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hforall
  have hcard : Monoid.exponent Kˣ = 2 ^ n - 1 := by
    rw [IsCyclic.exponent_eq_card, Nat.card_units, hK]
  rwa [hcard] at hexp

private lemma coeff_zero_of_torus [Fintype K] [CharP K 2] [NeZero n] {Φ : K → K → K}
    {a : Fin n → Fin n → K} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hlt : 2 ^ (n - 1) < Fintype.card K)
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (htor : ∀ c : K, c ≠ 0 → ∀ p : K, ∃ w : K, ∀ t : K,
      Φ (c * p) (c ^ 2 * t) = c * Φ p t + t * w)
    {i j : Fin n} (hj : j ≠ 0)
    (hne : (i, j) ≠ (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)) : a i j = 0 := by
  by_contra hij
  have htor' : ∀ c : K, c ≠ 0 → ∀ p t : K,
      eta Φ (c * p) (c ^ 2 * t) = c * eta Φ p t + c ^ 3 * t * eta Φ p (c⁻¹ ^ 2) :=
    fun c hc p t => eta_torus htor hc p t
  have hcoef : ∀ c : K, c ≠ 0 →
      a i j * c ^ (2 ^ (i : ℕ) + 2 ^ ((j : ℕ) + 1)) = c * a i j := by
    intro c hc
    have hfam := coeff_torus_family hlt ha htor' hc
    have h := congrFun (congrFun hfam i) j
    simpa [hj] using h
  have hdvd := dvd_of_coeff_torus hn hK hij hcoef
  have hposj : 1 ≤ (j : ℕ) := by
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      exact hj (Fin.ext h)
    omega
  have hne' : ((i : ℕ), (j : ℕ)) ≠ (n - 1, n - 2) := by
    intro h
    have h1 : (i : ℕ) = n - 1 := congrArg Prod.fst h
    have h2 : (j : ℕ) = n - 2 := congrArg Prod.snd h
    exact hne (Prod.ext (Fin.ext h1) (Fin.ext h2))
  exact not_dvd_two_pow_add_sub_one hn i.isLt hposj j.isLt hne' hdvd

private lemma eta_symm [CharP K 2] {Φ : K → K → K}
    (hsym : ∃ w : K → K, ∀ s t : K, Φ s t + t * w s = Φ t s + s * w t) (s t : K) :
    eta Φ s t + t * eta Φ 1 s = eta Φ t s + s * eta Φ 1 t := by
  obtain ⟨w, hw⟩ := hsym
  let ω : K → K := fun s => Φ s 1 + w s
  have hω1 : ∀ s t : K, eta Φ s t + t * ω s = eta Φ t s + s * ω t := by
    intro s t
    have h := hw s t
    simp only [eta, ω]
    linear_combination h + (t * Φ s 1 - s * Φ t 1) *
      (CharTwo.two_eq_zero : (2 : K) = 0)
  have hω2 : ∀ s : K, ω s = eta Φ 1 s + s * ω 1 := by
    intro s
    have h := hω1 s 1
    have h1 : eta Φ s 1 = 0 := eta_one s
    rw [h1, one_mul] at h
    simpa using h
  have h1 : eta Φ s t + t * (eta Φ 1 s + s * ω 1) =
      eta Φ t s + s * (eta Φ 1 t + t * ω 1) := by
    rw [← hω2 s, ← hω2 t]
    exact hω1 s t
  have h2 : eta Φ s t + t * eta Φ 1 s + (t * s * ω 1) =
      eta Φ t s + s * eta Φ 1 t + (s * t * ω 1) := by
    calc
      eta Φ s t + t * eta Φ 1 s + (t * s * ω 1)
          = eta Φ s t + t * (eta Φ 1 s + s * ω 1) := by ring
      _ = eta Φ t s + s * (eta Φ 1 t + t * ω 1) := h1
      _ = eta Φ t s + s * eta Φ 1 t + (s * t * ω 1) := by ring
  have hst : t * s * ω 1 = s * t * ω 1 := by ring
  rw [hst] at h2
  exact add_right_cancel h2

private lemma coeff_last_zero {n : ℕ} [Fintype K] [CharP K 2] [NeZero n] (hn : 3 ≤ n)
    (hlt : 2 ^ (n - 1) < Fintype.card K) {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (hsym : ∀ s t : K, eta Φ s t + t * eta Φ 1 s = eta Φ t s + s * eta Φ 1 t)
    (hkill : ∀ i j : Fin n, j ≠ 0 →
      (i, j) ≠ (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) → a i j = 0) :
    a ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ = 0 := by
  have hpoint : ∀ s t : K,
      (∑ i : Fin n, ∑ j : Fin n,
        (a i j + (if j = 0 then ∑ l : Fin n, a l i else 0)) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ))) =
      (∑ i : Fin n, ∑ j : Fin n,
        (a j i + (if i = 0 then ∑ l : Fin n, a l j else 0)) *
        (s ^ 2 ^ (i : ℕ) * t ^ 2 ^ (j : ℕ))) := by
    intro s t
    rw [← eta_symm_lhs_expand ha s t, ← eta_symm_rhs_expand ha s t]
    exact hsym s t
  have hfam := coeff_eq_of_bilin_expansion hlt hpoint
  have hcoeff := congrFun (congrFun hfam ⟨n - 1, by omega⟩) ⟨n - 2, by omega⟩
  have hj0 : (⟨n - 2, by omega⟩ : Fin n) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hi0 : (⟨n - 1, by omega⟩ : Fin n) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp only [if_neg hj0, if_neg hi0, add_zero] at hcoeff
  have hji : a ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 0 := by
    refine hkill ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ hi0 ?_
    intro h
    have h1 : (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := congrArg Prod.fst h
    have h2 : n - 2 = n - 1 := congrArg Fin.val h1
    omega
  rw [hcoeff, hji]

private lemma coeff_all_zero {n : ℕ} [Fintype K] [CharP K 2] [NeZero n]
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hlt : 2 ^ (n - 1) < Fintype.card K) {Φ : K → K → K} {a : Fin n → Fin n → K}
    (ha : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j * (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)))
    (htor : ∀ c : K, c ≠ 0 → ∀ p : K, ∃ w : K, ∀ t : K,
      Φ (c * p) (c ^ 2 * t) = c * Φ p t + t * w)
    (hsym : ∀ s t : K, eta Φ s t + t * eta Φ 1 s = eta Φ t s + s * eta Φ 1 t) :
    ∀ i j : Fin n, a i j = 0 := by
  have hkill5 : ∀ i j : Fin n, j ≠ 0 →
      (i, j) ≠ (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) → a i j = 0 :=
    fun i j hj hne => coeff_zero_of_torus hn hK hlt ha htor hj hne
  have hkill : ∀ i j : Fin n, j ≠ 0 → a i j = 0 := by
    intro i j hj
    by_cases hne : (i, j) = (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
    · have hj0 : (j : ℕ) = n - 2 := by
        have := congrArg (fun p : Fin n × Fin n => (p.2 : ℕ)) hne
        simpa using this
      have hjne : (j : ℕ) ≠ 0 := by
        intro h
        exact hj (Fin.ext h)
      have hn3 : 3 ≤ n := by omega
      have hlast := coeff_last_zero hn3 hlt ha hsym hkill5
      have hi : i = ⟨n - 1, by omega⟩ := congrArg Prod.fst hne
      have hj' : j = ⟨n - 2, by omega⟩ := congrArg Prod.snd hne
      rwa [hi, hj']
    · exact hkill5 i j hj hne
  have hcolfun : (fun i : Fin n => ∑ j : Fin n, a i j) = 0 := by
    refine CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_mul_pow_eq_zero
      (p := 2) hlt (a := fun i : Fin n => ∑ j : Fin n, a i j) ?_
    intro p
    have h := ha p 1
    rw [eta_one p] at h
    simp only [one_pow, mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  have hcolzero : ∀ i : Fin n, a i (0 : Fin n) = 0 := by
    intro i
    have hsum : (∑ j : Fin n, a i j) = a i (0 : Fin n) := by
      refine Finset.sum_eq_single (0 : Fin n) ?_ ?_
      · intro j _ hj
        exact hkill i j hj
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h := congrFun hcolfun i
    rwa [hsum] at h
  have ha_all : ∀ i j : Fin n, a i j = 0 := by
    intro i j
    by_cases hj : j = 0
    · subst j
      exact hcolzero i
    · exact hkill i j hj
  exact ha_all

private theorem eta_eq_zero_of_torus_symm {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (Φ : K → K → K)
    (hadd : ∀ p s t : K, Φ p (s + t) = Φ p s + Φ p t)
    (hmod : ∀ p p' : K, ∃ w : K, ∀ t : K, Φ (p + p') t = Φ p t + Φ p' t + t * w)
    (htor : ∀ c : K, c ≠ 0 → ∀ p : K, ∃ w : K, ∀ t : K,
      Φ (c * p) (c ^ 2 * t) = c * Φ p t + t * w)
    (hsym : ∃ w : K → K, ∀ s t : K, Φ s t + t * w s = Φ t s + s * w t) :
    ∀ p t : K, eta Φ p t = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (by norm_num) n).ne')
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero n := ⟨by omega⟩
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hη_add : ∀ p s t : K, eta Φ p (s + t) = eta Φ p s + eta Φ p t :=
    fun p => eta_add_right hadd p
  have hη_addp : ∀ p p' t : K, eta Φ (p + p') t = eta Φ p t + eta Φ p' t :=
    fun p p' t => eta_add_left hmod p p' t
  let ηa : K → K →+ K := fun p => AddMonoidHom.mk' (eta Φ p) (hη_add p)
  have hη_addp' : ∀ p p' : K, ηa (p + p') = ηa p + ηa p' := by
    intro p p'
    ext t
    simpa [ηa] using hη_addp p p' t
  let ηb : K →+ K →+ K := AddMonoidHom.mk' ηa hη_addp'
  obtain ⟨a, ha, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
      Nat.prime_two (by omega) hK).2.1 ηb
  have ha' : ∀ x y : K, eta Φ x y = ∑ i, ∑ j, a i j *
      (x ^ 2 ^ (i : ℕ) * y ^ 2 ^ (j : ℕ)) := by
    intro x y
    simpa [ηb, ηa] using ha x y
  have hsym' : ∀ s t : K, eta Φ s t + t * eta Φ 1 s = eta Φ t s + s * eta Φ 1 t :=
    fun s t => eta_symm hsym s t
  have ha_all := coeff_all_zero hn hK hlt ha' htor hsym'
  intro p t
  rw [ha' p t]
  simp [ha_all]

theorem coboundary_of_torus_symm {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (Φ : K → K → K)
    (hadd : ∀ p s t, Φ p (s + t) = Φ p s + Φ p t)
    (hmod : ∀ p p', ∃ w : K, ∀ t, Φ (p + p') t = Φ p t + Φ p' t + t * w)
    (htor : ∀ c : K, c ≠ 0 → ∀ p, ∃ w : K, ∀ t, Φ (c * p) (c ^ 2 * t) = c * Φ p t + t * w)
    (hsym : ∃ w : K → K, ∀ s t, Φ s t + t * w s = Φ t s + s * w t) :
    ∀ p, ∃ w : K, ∀ t, Φ p t = t * w := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  intro p
  refine ⟨Φ p 1, fun t => ?_⟩
  have h := eta_eq_zero_of_torus_symm hn hK Φ hadd hmod htor hsym p t
  have h' : Φ p t = -(t * Φ p 1) := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at h'

end CFSG.Quasithin.St84
