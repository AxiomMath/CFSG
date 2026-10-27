module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KE.CTCyclo

open Polynomial

@[expose] def cycloIdx : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 24, 30]

theorem cyc_of_mul {n : ℕ} (hn : 0 < n) {P : ℤ[X]}
    (hP : P * ∏ d ∈ n.properDivisors, cyclotomic d ℤ = X ^ n - 1) :
    cyclotomic n ℤ = P := by
  have h := prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have hrest0 : ∏ d ∈ n.properDivisors, cyclotomic d ℤ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun d _ => cyclotomic_ne_zero d ℤ
  rw [← Nat.cons_self_properDivisors hn.ne', Finset.prod_cons] at h
  exact mul_right_cancel₀ hrest0 (h.trans hP.symm)

theorem cyclotomic_int_1 : cyclotomic 1 ℤ = X - 1 := cyclotomic_one ℤ

theorem cyclotomic_int_2 : cyclotomic 2 ℤ = X + 1 := cyclotomic_two ℤ

theorem cyclotomic_int_3 : cyclotomic 3 ℤ = X ^ 2 + X + 1 := cyclotomic_three ℤ

theorem cyclotomic_int_4 : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 4 = {1, 2} from by decide, Finset.prod_insert (by decide),
    Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2]
  ring

theorem cyclotomic_int_5 : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  ring

theorem cyclotomic_int_6 : cyclotomic 6 ℤ = X ^ 2 - X + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 6 = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2,
    cyclotomic_int_3]
  ring

theorem cyclotomic_int_7 : cyclotomic 7 ℤ = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  ring

theorem cyclotomic_int_8 : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 8 = {1, 2, 4} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2,
    cyclotomic_int_4]
  ring

theorem cyclotomic_int_10 : cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 10 = {1, 2, 5} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2,
    cyclotomic_int_5]
  ring

theorem cyclotomic_int_12 : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 12 = {1, 2, 3, 4, 6} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2, cyclotomic_int_3, cyclotomic_int_4,
    cyclotomic_int_6]
  ring

theorem cyclotomic_int_14 :
    cyclotomic 14 ℤ = X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 14 = {1, 2, 7} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2,
    cyclotomic_int_7]
  ring

theorem cyclotomic_int_15 :
    cyclotomic 15 ℤ = X ^ 8 - X ^ 7 + X ^ 5 - X ^ 4 + X ^ 3 - X + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 15 = {1, 3, 5} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_3,
    cyclotomic_int_5]
  ring

theorem cyclotomic_int_20 : cyclotomic 20 ℤ = X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 20 = {1, 2, 4, 5, 10} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2, cyclotomic_int_4, cyclotomic_int_5,
    cyclotomic_int_10]
  ring

theorem cyclotomic_int_24 : cyclotomic 24 ℤ = X ^ 8 - X ^ 4 + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 24 = {1, 2, 3, 4, 6, 8, 12} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2, cyclotomic_int_3, cyclotomic_int_4,
    cyclotomic_int_6, cyclotomic_int_8, cyclotomic_int_12]
  ring

theorem cyclotomic_int_30 :
    cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  refine cyc_of_mul (by norm_num) ?_
  rw [show Nat.properDivisors 30 = {1, 2, 3, 5, 6, 10, 15} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, cyclotomic_int_1, cyclotomic_int_2, cyclotomic_int_3, cyclotomic_int_5,
    cyclotomic_int_6, cyclotomic_int_10, cyclotomic_int_15]
  ring

theorem orderOf_eq_of_dvd_cyclotomic {p e q : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e)
    (h : (p : ℤ) ∣ (cyclotomic e ℤ).eval (q : ℤ)) : orderOf (q : ZMod p) = e := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : NeZero (e : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  have hroot : (cyclotomic e (ZMod p)).IsRoot (q : ZMod p) := by
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    rw [← map_cyclotomic e (Int.castRingHom (ZMod p)), IsRoot.def]
    have h2 := eval_intCast_map (Int.castRingHom (ZMod p)) (cyclotomic e ℤ) (q : ℤ)
    simp only [Int.cast_natCast] at h2
    rw [h2]
    simpa using h1
  exact (isRoot_cyclotomic_iff.1 hroot).eq_orderOf.symm

theorem not_dvd_of_mem_cycloIdx {p e : ℕ} (hp : p.Prime) (hp7 : 7 < p) (he : e ∈ cycloIdx) :
    ¬ p ∣ e := by
  intro h
  simp only [cycloIdx, List.mem_cons, List.not_mem_nil, or_false] at he
  have he0 : 0 < e := by omega
  have hp30 : p ≤ 30 := by
    have := Nat.le_of_dvd he0 h
    omega
  interval_cases p <;> rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> first | omega | (revert hp; decide)

theorem not_dvd_of_mem_indices {p d : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hd : d ∈ ([1, 2, 4, 5, 8, 9] : List ℕ)) : ¬ (p : ℤ) ∣ (d : ℤ) := by
  intro h
  have h' : p ∣ d := Int.natCast_dvd_natCast.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  have hd0 : 0 < d := by omega
  have hle := Nat.le_of_dvd hd0 h'
  have hp9 : p ≤ 9 := by omega
  interval_cases p <;> first | omega | (revert hp; decide)

theorem not_dvd_of_orderOf {p q m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hord : orderOf (q : ZMod p) = m) : ¬ p ∣ q := by
  intro hdvd
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  rw [(ZMod.natCast_eq_zero_iff q p).2 hdvd, orderOf_zero] at hord
  omega

theorem cast_f14 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 6 - q ^ 5 + q ^ 4 - q ^ 3 + q ^ 2 - q + 1 : ℕ) : ℤ) =
      (q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
  have h1 : q ^ 5 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ≤ q ^ 2 := Nat.le_self_pow (by omega) q
  have h4 : q ^ 3 ≤ q ^ 6 - q ^ 5 + q ^ 4 := by omega
  have h5 : q ≤ q ^ 6 - q ^ 5 + q ^ 4 - q ^ 3 + q ^ 2 := by omega
  zify [h1, h4, h5]

theorem cast_f15 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 8 - q ^ 7 + q ^ 5 - q ^ 4 + q ^ 3 - q + 1 : ℕ) : ℤ) =
      (q : ℤ) ^ 8 - (q : ℤ) ^ 7 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 + (q : ℤ) ^ 3 - (q : ℤ) + 1 := by
  have h1 : q ^ 7 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : q ^ 4 ≤ q ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ≤ q ^ 3 := Nat.le_self_pow (by omega) q
  have h4 : q ^ 4 ≤ q ^ 8 - q ^ 7 + q ^ 5 := by omega
  have h5 : q ≤ q ^ 8 - q ^ 7 + q ^ 5 - q ^ 4 + q ^ 3 := by omega
  zify [h1, h4, h5]

theorem cast_f30 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 8 + q ^ 7 - q ^ 5 - q ^ 4 - q ^ 3 + q + 1 : ℕ) : ℤ) =
      (q : ℤ) ^ 8 + (q : ℤ) ^ 7 - (q : ℤ) ^ 5 - (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) + 1 := by
  have h8 : 2 * q ^ 7 ≤ q ^ 8 :=
    calc 2 * q ^ 7 ≤ q * q ^ 7 := Nat.mul_le_mul_right _ hq
      _ = q ^ 8 := by ring
  have h5 : q ^ 5 ≤ q ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : q ^ 4 ≤ q ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : q ^ 5 ≤ q ^ 8 + q ^ 7 := by omega
  have e2 : q ^ 4 ≤ q ^ 8 + q ^ 7 - q ^ 5 := by omega
  have e3 : q ^ 3 ≤ q ^ 8 + q ^ 7 - q ^ 5 - q ^ 4 := by omega
  zify [e1, e2, e3]

theorem cast_f20 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 8 - q ^ 6 + q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) =
      (q : ℤ) ^ 8 - (q : ℤ) ^ 6 + (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
  have h1 : q ^ 6 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ^ 2 ≤ q ^ 8 - q ^ 6 + q ^ 4 := by omega
  zify [h1, h3]

theorem cast_f24 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 8 - q ^ 4 + 1 : ℕ) : ℤ) = (q : ℤ) ^ 8 - (q : ℤ) ^ 4 + 1 := by
  have h1 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  zify [h1]

theorem cast_f12 {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
  have h1 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  zify [h1]

end CFSG.RankThree.PartOne.KE.CTCyclo
