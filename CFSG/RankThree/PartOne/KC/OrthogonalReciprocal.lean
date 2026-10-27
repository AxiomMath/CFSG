module

public import Mathlib.Algebra.Polynomial.FieldDivision

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial

section Reverse

variable {K : Type*} [Field K]

theorem natTrailingDegree_eq_zero_of_coeff_zero_ne {p : K[X]} (h0 : p.coeff 0 ≠ 0) :
    p.natTrailingDegree = 0 :=
  natTrailingDegree_eq_zero.mpr (Or.inr h0)

theorem natDegree_reverse_of_coeff_zero_ne {p : K[X]} (h0 : p.coeff 0 ≠ 0) :
    p.reverse.natDegree = p.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero_of_coeff_zero_ne h0, Nat.sub_zero]

theorem reverse_reverse_of_coeff_zero_ne {p : K[X]} (h0 : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  calc p.reverse.reverse = reflect p.reverse.natDegree p.reverse := rfl
    _ = reflect p.natDegree (reflect p.natDegree p) := by
      rw [natDegree_reverse_of_coeff_zero_ne h0]; rfl
    _ = p := reflect_reflect

theorem coeff_zero_reverse_ne {p : K[X]} (hp : p ≠ 0) : p.reverse.coeff 0 ≠ 0 := by
  rw [coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr hp

theorem isUnit_of_natDegree_eq_zero_of_ne_zero {g : K[X]} (hg : g ≠ 0)
    (hdeg : g.natDegree = 0) : IsUnit g := by
  rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hg, hdeg]
  rfl

theorem irreducible_reverse {p : K[X]} (hp : Irreducible p) (h0 : p.coeff 0 ≠ 0) :
    Irreducible p.reverse := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hr0 : p.reverse.coeff 0 ≠ 0 := coeff_zero_reverse_ne hp0
  have hrr : p.reverse.reverse = p := reverse_reverse_of_coeff_zero_ne h0
  refine ⟨fun hu => hp.not_isUnit ?_, fun g h hgh => ?_⟩
  · have hdeg := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_reverse_of_coeff_zero_ne h0] at hdeg
    exact isUnit_of_natDegree_eq_zero_of_ne_zero hp0 hdeg
  · have hg0 : g.coeff 0 ≠ 0 := fun h' => hr0 (by rw [hgh, mul_coeff_zero, h', zero_mul])
    have hh0 : h.coeff 0 ≠ 0 := fun h' => hr0 (by rw [hgh, mul_coeff_zero, h', mul_zero])
    have hmul : p = g.reverse * h.reverse := by
      rw [← reverse_mul_of_domain, ← hgh, hrr]
    rcases hp.isUnit_or_isUnit hmul with hu | hu
    · left
      have hdeg := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_reverse_of_coeff_zero_ne hg0] at hdeg
      exact isUnit_of_natDegree_eq_zero_of_ne_zero (fun h' => hg0 (by rw [h']; rfl)) hdeg
    · right
      have hdeg := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_reverse_of_coeff_zero_ne hh0] at hdeg
      exact isUnit_of_natDegree_eq_zero_of_ne_zero (fun h' => hh0 (by rw [h']; rfl)) hdeg

theorem reverse_C_mul (c : K) (f : K[X]) (hc : c ≠ 0) :
    (C c * f).reverse = C c * f.reverse := by
  rw [reverse, reverse, natDegree_C_mul hc, reflect_C_mul]

@[expose] noncomputable def reciprocalPolynomial (h : K[X]) : K[X] :=
  C (h.coeff 0)⁻¹ * h.reverse

theorem natDegree_reciprocalPolynomial {h : K[X]} (h0 : h.coeff 0 ≠ 0) :
    (reciprocalPolynomial h).natDegree = h.natDegree := by
  rw [reciprocalPolynomial, natDegree_C_mul (inv_ne_zero h0),
    natDegree_reverse_of_coeff_zero_ne h0]

theorem monic_reciprocalPolynomial {h : K[X]} (h0 : h.coeff 0 ≠ 0) :
    (reciprocalPolynomial h).Monic := by
  rw [Monic, reciprocalPolynomial, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
    trailingCoeff, natTrailingDegree_eq_zero_of_coeff_zero_ne h0]
  exact inv_mul_cancel₀ h0

theorem coeff_zero_reciprocalPolynomial {h : K[X]} (hm : h.Monic) :
    (reciprocalPolynomial h).coeff 0 = (h.coeff 0)⁻¹ := by
  rw [reciprocalPolynomial, coeff_C_mul, coeff_zero_reverse, hm.leadingCoeff, mul_one]

theorem reciprocalPolynomial_reciprocalPolynomial {h : K[X]} (hm : h.Monic)
    (h0 : h.coeff 0 ≠ 0) : reciprocalPolynomial (reciprocalPolynomial h) = h := by
  have h1 : reciprocalPolynomial (reciprocalPolynomial h) =
      C ((reciprocalPolynomial h).coeff 0)⁻¹ * (reciprocalPolynomial h).reverse := rfl
  have h2 : (reciprocalPolynomial h).reverse = C (h.coeff 0)⁻¹ * h := by
    rw [reciprocalPolynomial, reverse_C_mul _ _ (inv_ne_zero h0),
      reverse_reverse_of_coeff_zero_ne h0]
  rw [h1, coeff_zero_reciprocalPolynomial hm, inv_inv, h2, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ h0, C_1, one_mul]

theorem irreducible_reciprocalPolynomial {h : K[X]} (hirr : Irreducible h) (h0 : h.coeff 0 ≠ 0) :
    Irreducible (reciprocalPolynomial h) :=
  (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero h0)))).mpr
    (irreducible_reverse hirr h0)

theorem aeval_reflect_of_unit {A : Type*} [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) {N : ℕ}
    (hN : f.natDegree ≤ N) :
    aeval (u : A) (reflect N f) = (u : A) ^ N * aeval ((u⁻¹ : Aˣ) : A) f := by
  have h1 : (reflect N f).natDegree < N + 1 :=
    Nat.lt_succ_of_le ((natDegree_reflect_le (N := N) (p := f)).trans (max_le le_rfl hN))
  have h2 : f.natDegree < N + 1 := Nat.lt_succ_of_le hN
  rw [aeval_eq_sum_range' h1, aeval_eq_sum_range' h2, Finset.mul_sum]
  have h3 : ∀ i ∈ Finset.range (N + 1), (reflect N f).coeff i • (u : A) ^ i =
      f.coeff (N - i) • (u : A) ^ i := fun i hi => by
    rw [coeff_reflect, revAt_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [Finset.sum_congr rfl h3]
  rw [← Finset.sum_range_reflect (fun j => f.coeff (N - j) • (u : A) ^ j) (N + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show N + 1 - 1 - j = N - j by omega, show N - (N - j) = j by omega, mul_smul_comm]
  have h4 : (u : A) ^ (N - j) = (u : A) ^ N * ((u⁻¹ : Aˣ) : A) ^ j := by
    have : u ^ (N - j) = u ^ N * (u⁻¹) ^ j := by
      rw [pow_sub u hj', inv_pow]
    have h5 := congrArg (fun w : Aˣ => (w : A)) this
    simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h5
  rw [h4]

theorem aeval_reciprocalPolynomial_of_unit {A : Type*} [Ring A] [Algebra K A] (u : Aˣ)
    (h : K[X]) :
    aeval (u : A) (reciprocalPolynomial h) =
      (h.coeff 0)⁻¹ • ((u : A) ^ h.natDegree * aeval ((u⁻¹ : Aˣ) : A) h) := by
  rw [reciprocalPolynomial, map_mul, aeval_C, Algebra.smul_def, reverse,
    aeval_reflect_of_unit u h le_rfl]

end Reverse

end CFSG.RankThree.PartOne.KCOrthogonal
