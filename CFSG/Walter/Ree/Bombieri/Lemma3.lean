module

public import CFSG.Walter.Ree.Bombieri.Lemma3NT
public import CFSG.Walter.Ree.Bombieri.Appendix
import CFSG.Walter.Ree.Bombieri.Galois

public section

namespace CFSG.Walter.Ree.Bombieri

open MvPolynomial

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

@[expose] def expo {k : ℕ} (t : ℕ) (α : Fin (k + 1) →₀ ℕ) : ℕ := ∑ i, α i * 3 ^ (t * i)

omit [Fintype K] in
theorem eval_frob {k t : ℕ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ t)
    (H : MvPolynomial (Fin (k + 1)) (ZMod 3)) (z : K) :
    eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) H =
      ∑ α ∈ H.support, castThree K (H.coeff α) * z ^ expo t α := by
  rw [eval₂_eq']
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  simp only [pow_apply_of_eq_frob_pow hσ, ← pow_mul, expo]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem one_le_expo {k t : ℕ} {α : Fin (k + 1) →₀ ℕ} (hα : α ≠ 0) : 1 ≤ expo t α := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra h; push Not at h; exact hα (Finsupp.ext h)
  calc 1 ≤ α i * 3 ^ (t * i) := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hi (by positivity))
    _ ≤ expo t α := Finset.single_le_sum (f := fun j => α j * 3 ^ (t * j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

omit [Fintype K] in
theorem coeff_zero_eq_zero {k t : ℕ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ t)
    {H : MvPolynomial (Fin (k + 1)) (ZMod 3)}
    (hvan : ∀ z : K, eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) H = 0) :
    H.coeff 0 = 0 := by
  have h := hvan 0
  rw [eval_frob hσ] at h
  by_cases h0 : (0 : Fin (k + 1) →₀ ℕ) ∈ H.support
  · rw [Finset.sum_eq_single 0 (fun α _ hα => by
      rw [zero_pow (by have := one_le_expo (t := t) hα; omega), mul_zero])
      (fun h' => absurd h0 h')] at h
    simp only [expo, Finsupp.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      pow_zero, mul_one] at h
    exact (castThree K).injective (by rw [h, map_zero])
  · simpa using h0

theorem exists_collision {m k t : ℕ} (hK : Fintype.card K = 3 ^ m) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 3 ^ t) {H : MvPolynomial (Fin (k + 1)) (ZMod 3)} (hH : H ≠ 0)
    (hvan : ∀ z : K, eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) H = 0) :
    ∃ α ∈ H.support, ∃ β ∈ H.support, α ≠ β ∧
      expo t α % (3 ^ m - 1) = expo t β % (3 ^ m - 1) := by
  classical
  by_contra hcon
  push Not at hcon
  have hq : 1 < 3 ^ m - 1 := by
    have := Fintype.one_lt_card (α := K)
    have h2 : 3 ^ m ≠ 2 := by
      intro h; have := congrArg (· % 3) h; simp at this
      rcases m with _ | m
      · simp at this
      · simp [pow_succ] at this
    omega
  set q1 := 3 ^ m - 1
  let g : Polynomial K := ∑ α ∈ H.support,
    Polynomial.C (castThree K (H.coeff α)) * Polynomial.X ^ (expo t α % q1)
  have hg : g = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero g (ι := Kˣ)
      (f := Units.val) Units.val_injective (fun z => ?_) ?_
    · have h := hvan z
      rw [eval_frob hσ] at h
      rw [← h, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      congr 1
      have hmod : expo t α % q1 ≡ expo t α [MOD Fintype.card K - 1] := by
        rw [hK]; exact Nat.mod_modEq _ _
      exact pow_eq_pow_of_modEq hmod z.ne_zero
    · rw [Fintype.card_units, hK]
      refine (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := q1 - 1) fun α _ => ?_).trans_lt
        (by omega)
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have := Nat.mod_lt (expo t α) (show 0 < q1 by omega)
      omega
  obtain ⟨α₀, hα₀⟩ := (MvPolynomial.support_nonempty).mpr hH
  have hc := congrArg (fun p : Polynomial K => p.coeff (expo t α₀ % q1)) hg
  simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
    at hc
  rw [Finset.sum_eq_single α₀
      (fun β hβ hne => by rw [ite_eq_right (hcon α₀ hα₀ β hβ (Ne.symm hne))])
      (fun h => absurd hα₀ h), ite_eq_left rfl] at hc
  exact (mem_support_iff.mp hα₀) ((castThree K).injective (by rw [hc, map_zero]))

theorem isCoprime_three_pow (a : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    IsCoprime ((3 : ℤ) ^ a) ((3 : ℤ) ^ m - 1) := by
  refine IsCoprime.pow_left ?_
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact ⟨3 ^ m, -1, by ring⟩

theorem lemma3 {m k t d : ℕ} (hK : Fintype.card K = 3 ^ m) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 3 ^ t) (hk : 1 ≤ k) {H : MvPolynomial (Fin (k + 1)) (ZMod 3)}
    (hH : H ≠ 0) (hdeg : ∀ i, H.degreeOf i + 2 ≤ 3 ^ d)
    (hvan : ∀ z : K, eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) H = 0) :
    ∃ l lam : ℕ, 1 ≤ l ∧ l ≤ k ∧ lam < d ∧
      ((t * l : ℤ) ≡ lam [ZMOD m] ∨ (t * l + lam : ℤ) ≡ 0 [ZMOD m]) := by
  classical
  have hm : 1 ≤ m := by
    have := Fintype.one_lt_card (α := K)
    rw [hK] at this
    rcases m with _ | m
    · simp at this
    · omega
  have hd : 1 ≤ d := by
    have := hdeg 0
    rcases d with _ | d
    · simp at this
    · omega
  have h3d : 3 ≤ 3 ^ d := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  obtain ⟨α, hα, β, hβ, hne, hmod⟩ := exists_collision hK hσ hH hvan
  let a : ℕ → ℤ := fun i => if h : i < k + 1 then (α ⟨i, h⟩ : ℤ) - β ⟨i, h⟩ else 0
  have ha_bound : ∀ i, (a i).natAbs + 2 ≤ 3 ^ d := by
    intro i
    simp only [a]
    split_ifs with h
    · have h1 := monomial_le_degreeOf ⟨i, h⟩ hα
      have h2 := monomial_le_degreeOf ⟨i, h⟩ hβ
      have h3 := hdeg ⟨i, h⟩
      omega
    · simp; omega
  have ha_ne : ∃ j, a j ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra h; push Not at h; exact hne (Finsupp.ext h)
    refine ⟨i, ?_⟩
    simp only [a, i.2, dite_true, Fin.eta]
    omega
  have ha_zero : ∀ j, k < j → a j = 0 := fun j hj => by simp [a]; omega
  have hsum : ∑ i ∈ Finset.range (k + 1), a i * 3 ^ (t * i) = (expo t α : ℤ) - expo t β := by
    rw [Finset.sum_range, expo, expo]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a, i.2, dite_true, Fin.eta]
    ring
  have hdiv : ((3 : ℤ) ^ m - 1) ∣ ∑ i ∈ Finset.range (k + 1), a i * 3 ^ (t * i) := by
    rw [hsum]
    have h1 : ((3 ^ m - 1 : ℕ) : ℤ) = (3 : ℤ) ^ m - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
    rw [← h1, ← dvd_neg, neg_sub]
    exact Nat.modEq_iff_dvd.mp hmod
  set j0 := Nat.find ha_ne with hj0def
  have hj0 : a j0 ≠ 0 := Nat.find_spec ha_ne
  have hlt0 : ∀ j < j0, a j = 0 := fun j hj => by
    by_contra h; exact Nat.find_min ha_ne hj h
  have hj0k : j0 ≤ k := by
    by_contra h; exact hj0 (ha_zero j0 (by omega))
  set b : ℕ → ℤ := fun i => a (i + j0) with hb
  have hsum_shift : ∑ i ∈ Finset.range (k + 1), a i * 3 ^ (t * i) =
      3 ^ (t * j0) * ∑ i ∈ Finset.range (k + 1), b i * 3 ^ (t * i) := by
    have e1 : ∑ i ∈ Finset.range (k + 1), a i * 3 ^ (t * i) =
        ∑ i ∈ Finset.range (j0 + (k + 1)), a i * 3 ^ (t * i) := by
      rw [show j0 + (k + 1) = (k + 1) + j0 by ring,
        Finset.sum_range_add (fun i => a i * 3 ^ (t * i)) (k + 1) j0,
        Finset.sum_eq_zero (s := Finset.range j0) (fun i _ => by
          rw [ha_zero _ (by omega), zero_mul]), add_zero]
    rw [e1, Finset.sum_range_add (fun i => a i * 3 ^ (t * i)) j0 (k + 1), Finset.mul_sum,
      Finset.sum_eq_zero (fun i hi => by rw [hlt0 i (by simpa using hi), zero_mul]), zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [b]
    rw [show j0 + i = i + j0 by ring, mul_add, pow_add]
    ring
  have hdivb : ((3 : ℤ) ^ m - 1) ∣ ∑ i ∈ Finset.range (k + 1), b i * 3 ^ (t * i) := by
    rw [hsum_shift] at hdiv
    exact (isCoprime_three_pow _ hm).symm.dvd_of_dvd_mul_left hdiv
  exact lemma3_arith hm hd hk b (by simpa [b] using hj0) (fun i _ => ha_bound _) hdivb

end CFSG.Walter.Ree.Bombieri
