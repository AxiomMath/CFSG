module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial

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


section Dual

variable {σ : K →+* K}

@[expose] noncomputable def dualPoly (σ : K →+* K) (a : K[X]) : K[X] :=
  C (σ (a.coeff 0))⁻¹ * (a.map σ).reverse

theorem coeff_zero_map_ne {a : K[X]} (h0 : a.coeff 0 ≠ 0) : (a.map σ).coeff 0 ≠ 0 := by
  rw [coeff_map]
  exact (map_ne_zero σ).mpr h0

theorem natDegree_dualPoly {a : K[X]} (h0 : a.coeff 0 ≠ 0) :
    (dualPoly σ a).natDegree = a.natDegree := by
  have hc : (σ (a.coeff 0))⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr h0)
  rw [dualPoly, natDegree_C_mul hc, natDegree_reverse_of_coeff_zero_ne (coeff_zero_map_ne h0),
    natDegree_map]

theorem monic_dualPoly {a : K[X]} (h0 : a.coeff 0 ≠ 0) :
    (dualPoly σ a).Monic := by
  have h1 : σ (a.coeff 0) ≠ 0 := (map_ne_zero σ).mpr h0
  rw [Monic, dualPoly, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff,
    natTrailingDegree_eq_zero_of_coeff_zero_ne (coeff_zero_map_ne h0), coeff_map]
  exact inv_mul_cancel₀ h1

theorem coeff_zero_dualPoly {a : K[X]} (ha : a.Monic) :
    (dualPoly σ a).coeff 0 = (σ (a.coeff 0))⁻¹ := by
  rw [dualPoly, coeff_C_mul, coeff_zero_reverse, leadingCoeff_map, ha.leadingCoeff, map_one,
    mul_one]

theorem coeff_zero_dualPoly_ne {a : K[X]} (ha : a.Monic) (h0 : a.coeff 0 ≠ 0) :
    (dualPoly σ a).coeff 0 ≠ 0 := by
  rw [coeff_zero_dualPoly ha]
  exact inv_ne_zero ((map_ne_zero σ).mpr h0)

theorem map_reverse (f : K[X]) : (f.reverse).map σ = (f.map σ).reverse := by
  rw [reverse, reverse, natDegree_map, reflect_map]

theorem reverse_C_mul (c : K) (f : K[X]) (hc : c ≠ 0) :
    (C c * f).reverse = C c * f.reverse := by
  rw [reverse, reverse, natDegree_C_mul hc, reflect_C_mul]

theorem dualPoly_dualPoly (hσ : Function.Involutive σ) {a : K[X]} (ha : a.Monic)
    (h0 : a.coeff 0 ≠ 0) : dualPoly σ (dualPoly σ a) = a := by
  have hσ0 : σ (a.coeff 0) ≠ 0 := (map_ne_zero σ).mpr h0
  have hmm : (a.map σ).map σ = a := by
    rw [Polynomial.map_map]
    have : σ.comp σ = RingHom.id K := RingHom.ext hσ
    rw [this, map_id]
  have hd : (dualPoly σ a).map σ = C (a.coeff 0)⁻¹ * a.reverse := by
    rw [dualPoly, Polynomial.map_mul, map_C, map_reverse, hmm, map_inv₀, hσ]
  have h3 : σ ((σ (a.coeff 0))⁻¹) = (a.coeff 0)⁻¹ := by rw [map_inv₀, hσ]
  rw [dualPoly, coeff_zero_dualPoly ha, h3, hd, inv_inv, reverse_C_mul _ _ (inv_ne_zero h0),
    reverse_reverse_of_coeff_zero_ne h0, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h0, C_1, one_mul]

theorem irreducible_dualPoly (hσ : Function.Involutive σ) {a : K[X]} (ha : Irreducible a)
    (h0 : a.coeff 0 ≠ 0) : Irreducible (dualPoly σ a) := by
  let e : K ≃+* K := RingEquiv.ofBijective σ ⟨hσ.injective, hσ.surjective⟩
  have h1 : Irreducible (a.map σ) := by
    have h := (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mpr ha
    rw [Polynomial.mapEquiv_apply] at h
    have he : (e : K →+* K) = σ := RingHom.ext fun _ => rfl
    rwa [he] at h
  have h2 := irreducible_reverse h1 (coeff_zero_map_ne h0)
  have hc : (σ (a.coeff 0))⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr h0)
  exact (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).mpr h2


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

end Dual

end CFSG.RankThree.PartOne.KCUnitary
