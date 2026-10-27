module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.FrobeniusMonomials

theorem rotate_injOn {n : ℕ} {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n) :
    Set.InjOn (fun i => (i + n - 1) % n) ↑J := by
  intro i hi j hj hij
  have hi' : i < n := hJn i hi
  have hj' : j < n := hJn j hj
  have hmi : i + n - 1 ∈ Finset.Ico (n - 1) (n - 1 + n) := by
    simp only [Finset.mem_Ico]
    omega
  have hmj : j + n - 1 ∈ Finset.Ico (n - 1) (n - 1 + n) := by
    simp only [Finset.mem_Ico]
    omega
  have h := Nat.mod_injOn_Ico (n - 1) n hmi hmj hij
  omega

theorem pow_two_pow_pred_mul_sum {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (J : Finset ℕ) (hJ : ∀ i ∈ J, i < n) (x : F) :
    x ^ (2 ^ (n - 1) * ∑ i ∈ J, 2 ^ i) =
      x ^ (∑ i ∈ J.image (fun i => (i + n - 1) % n), 2 ^ i) := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · simp
  obtain ⟨i₀, hi₀⟩ := hJne
  have hn : 1 ≤ n := by
    have := hJ i₀ hi₀
    omega
  have hpow : ∀ k : ℕ, x ^ (2 ^ n * k) = x ^ k := by
    intro k
    rw [pow_mul, show x ^ 2 ^ n = x from by rw [← hF]; exact FiniteField.pow_card x]
  have key : ∀ i ∈ J, x ^ (2 ^ (n - 1) * 2 ^ i) = x ^ (2 ^ ((i + n - 1) % n)) := by
    intro i hi
    have hi' : i < n := hJ i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [pow_zero, mul_one]
      rw [show (0 + n - 1) % n = n - 1 by
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]]
    · have hmod : (i + n - 1) % n = i - 1 := by
        rw [show i + n - 1 = (i - 1) + n by omega]
        exact Nat.mod_eq_of_modEq Nat.add_modEq_right (by omega)
      rw [hmod]
      have hmul : 2 ^ (n - 1) * 2 ^ i = 2 ^ n * 2 ^ (i - 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      rw [hmul, hpow]
  have hinj : Set.InjOn (fun i => (i + n - 1) % n) ↑J := rotate_injOn hJ
  rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, Finset.prod_congr rfl key,
    Finset.prod_pow_eq_pow_sum, Finset.sum_image hinj]

theorem add_pow_aexp {R : Type*} [CommRing R] [CharP R 2] (J : Finset ℕ) (s t : R) :
    (s + t) ^ (∑ i ∈ J, 2 ^ i) =
      ∑ x : J → Fin 2, s ^ (∑ i : J, (x i : ℕ) * 2 ^ (i : ℕ)) *
        t ^ (∑ i : J, ((1 - x i : Fin 2) : ℕ) * 2 ^ (i : ℕ)) := by
  classical
  rw [← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ J, (s + t) ^ 2 ^ i =
      ∏ i : J, (s ^ 2 ^ (i : ℕ) + t ^ 2 ^ (i : ℕ)) := by
    rw [← Finset.prod_attach J (fun i : ℕ => (s + t) ^ 2 ^ i), Finset.univ_eq_attach]
    exact Finset.prod_congr rfl fun i _ => add_pow_char_pow s t 2 (i : ℕ)
  rw [h1]
  have h2 : ∏ i : J, (s ^ 2 ^ (i : ℕ) + t ^ 2 ^ (i : ℕ)) =
      ∏ i : J, ∑ j : Fin 2, s ^ ((j : ℕ) * 2 ^ (i : ℕ)) *
        t ^ (((1 - j : Fin 2) : ℕ) * 2 ^ (i : ℕ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two]
    simp [add_comm]
  rw [h2, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum]

theorem sum_filter_eq_zero_of_forall_eval {F E ι : Type*} [Field F] [Fintype F] [Field E]
    [Algebra F E] (s : Finset ι) (a : ι → ℕ) (c : ι → E) (ha : ∀ i ∈ s, a i < Fintype.card F)
    (h : ∀ x : F, ∑ i ∈ s, c i * algebraMap F E x ^ a i = 0) (m : ℕ) :
    ∑ i ∈ s with a i = m, c i = 0 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  set p : Polynomial E := ∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ a i with hp
  have hsup : s.sup a < Fintype.card F := by
    obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup s hs a
    rw [hsup]
    exact ha i hi
  have hdeg : p.natDegree < Fintype.card F := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := s.sup a) ?_) hsup
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.le_sup (f := a) hi)
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun x : F => algebraMap F E x) (algebraMap F E).injective (fun x => ?_) hdeg
    simp only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact h x
  have hcoeff := congrArg (fun q : Polynomial E => q.coeff m) hp0
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_filter]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hcoeff
  by_cases hc : a i = m
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (Ne.symm hc)]

end CFSG.FrobeniusMonomials
