module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

theorem dvd_of_mul_dvd_mul_left' {e f d : ℕ} (hf : 0 < f) (h : e * f ∣ f * d) : e ∣ d := by
  rw [mul_comm] at h
  exact Nat.dvd_of_mul_dvd_mul_left hf h

theorem odd_dvd_of_dvd_two_mul {e i : ℕ} (he : Odd e) (h : e ∣ 2 * i) : e ∣ i :=
  (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr he))) h

theorem exists_odd_near (n : ℕ) (hn : 4 ≤ n) : ∃ e, Odd e ∧ n - 1 ≤ e ∧ e ≤ n ∧ 3 ≤ e := by
  rcases Nat.even_or_odd n with h | h
  · refine ⟨n - 1, ?_, le_rfl, Nat.sub_le n 1, by omega⟩
    obtain ⟨r, hr⟩ := h
    exact ⟨r - 1, by omega⟩
  · exact ⟨n, h, Nat.sub_le n 1, le_rfl, by obtain ⟨r, hr⟩ := h; omega⟩

theorem lin_psl_arith {n k : ℕ} (hn : 4 ≤ n) (hk : n + 2 ≤ k)
    (hw : (k - 1) * k ≤ (n + 1) * (n + 2) + 4) : k = n + 2 := by
  by_contra hne
  have hk3 : n + 3 ≤ k := by omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hw
  nlinarith

theorem lin_psp_arith_trans {n k : ℕ} (hn : 4 ≤ n) (hk : n + 1 ≤ k)
    (hw : 2 * (k * k) ≤ (n + 1) * (n + 2) + 4) : False := by
  nlinarith

theorem lin_psp_arith_long {n k e : ℕ} (hn : 4 ≤ n) (he : n - 1 ≤ e) (hek : e + 2 ≤ k)
    (hw : 2 * (k * k) ≤ (n + 1) * (n + 2) + 4) : False :=
  lin_psp_arith_trans hn (by omega) hw

theorem lin_omega_arith {n k e : ℕ} (hn : 4 ≤ n) (he : n - 1 ≤ e) (hen : e ≤ n) (heo : Odd e)
    (hek : e ≤ k) (hlo : (n + 1) * (n + 2) ≤ 2 * (k * (k - 1)))
    (hw : 2 * (k * (k - 1)) ≤ (n + 1) * (n + 2) + 4) : n = 6 ∧ k = 6 := by
  obtain ⟨r, rfl⟩ := heo
  have hk : n - 1 ≤ k := le_trans he hek
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlo hw
  have hn9 : n ≤ 9 := by
    by_contra h9
    have hj : n - 2 ≤ j := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel] at hj
    nlinarith
  have hj9 : j ≤ 9 := by nlinarith
  interval_cases n <;> interval_cases j <;> omega

theorem lin_exc_arith {n N : ℕ} (hn : 4 ≤ n)
    (hN : N = 6 ∨ N = 12 ∨ N = 24 ∨ N = 36 ∨ N = 63 ∨ N = 120)
    (hlo : (n + 1) * (n + 2) ≤ 2 * N) (hw : 2 * N ≤ (n + 1) * (n + 2) + 4) :
    (N = 36 ∧ n = 7) ∨ (N = 120 ∧ n = 14) := by
  have hn15 : n ≤ 15 := by
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> nlinarith
  interval_cases n <;> rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end CFSG.RankThree.GF2n.Smith81.Insp
