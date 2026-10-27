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

namespace CFSG.Quasithin.H13.NQCore.L3Odd

theorem sq_sub_one_mul_cube_sub_one {p : ℕ} (hp : 1 ≤ p) :
    (p ^ 2 - 1) * (p ^ 3 - 1) = (p - 1) ^ 2 * ((p + 1) * (p ^ 2 + p + 1)) := by
  zify [hp, Nat.one_le_pow 2 p hp, Nat.one_le_pow 3 p hp]
  ring

theorem false_of_two_pow_dvd {p k m z N : ℕ} (hp : Odd p) (hz : ¬ 2 ∣ z) (hm : ¬ 2 ∣ m)
    (hN : N * z = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))) (hkm : 2 ^ k * m = N)
    (hdvd : 2 ^ k ∣ p ^ 3 * (p - 1) ^ 2) : False := by
  have hp1 : 1 ≤ p := hp.pos
  have hcop : Nat.Coprime (2 ^ k) (p ^ 3) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_two_left).2 hp)
  obtain ⟨w, hw⟩ : 2 ^ k ∣ (p - 1) ^ 2 := hcop.dvd_of_dvd_mul_left hdvd
  rw [sq_sub_one_mul_cube_sub_one hp1] at hN
  have h1 : 2 ^ k * (m * z) = 2 ^ k * (p ^ 3 * (w * ((p + 1) * (p ^ 2 + p + 1)))) := by
    calc 2 ^ k * (m * z) = N * z := by rw [← hkm]; ring
      _ = p ^ 3 * ((p - 1) ^ 2 * ((p + 1) * (p ^ 2 + p + 1))) := hN
      _ = _ := by rw [hw]; ring
  have h2 : m * z = p ^ 3 * (w * ((p + 1) * (p ^ 2 + p + 1))) :=
    Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos k) h1
  have h3 : 2 ∣ p + 1 := by
    obtain ⟨a, rfl⟩ := hp
    exact ⟨a + 1, by ring⟩
  have h4 : 2 ∣ m * z := by
    rw [h2]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _) _
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h4 with h | h
  · exact hm h
  · exact hz h

end CFSG.Quasithin.H13.NQCore.L3Odd
