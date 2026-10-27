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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.Monster.B

open Matrix

variable {n : Type*}

@[expose] def DivTwoPow (k : ℕ) (Y : Matrix n n ℤ) : Prop := ∃ C : Matrix n n ℤ, Y = (2 ^ k : ℤ) • C

theorem DivTwoPow.mono {k l : ℕ} (hkl : l ≤ k) {Y : Matrix n n ℤ} (h : DivTwoPow k Y) :
    DivTwoPow l Y := by
  obtain ⟨C, rfl⟩ := h
  refine ⟨(2 ^ (k - l) : ℤ) • C, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hkl]

theorem eq_zero_of_forall_divTwoPow {Y : Matrix n n ℤ} (h : ∀ k, DivTwoPow k Y) : Y = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  by_contra hne
  obtain ⟨C, hC⟩ := h (Int.natAbs (Y i j))
  have hij : Y i j = 2 ^ (Int.natAbs (Y i j)) * C i j := by
    have := congrFun (congrFun hC i) j
    simpa [Matrix.smul_apply, smul_eq_mul] using this
  have hdvd : (2 ^ (Int.natAbs (Y i j)) : ℤ) ∣ Y i j := ⟨C i j, hij⟩
  have hdvd' : 2 ^ (Int.natAbs (Y i j)) ∣ Int.natAbs (Y i j) := by
    have := Int.natAbs_dvd_natAbs.2 hdvd
    simpa [Int.natAbs_pow] using this
  have hpos : 0 < Int.natAbs (Y i j) := Int.natAbs_pos.2 hne
  have hle := Nat.le_of_dvd hpos hdvd'
  exact absurd hle (not_le.2 Nat.lt_two_pow_self)

variable [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem divTwoPow_of_odd_smul {b : ℕ} (hb : Odd b) {k : ℕ} {C : Matrix n n ℤ}
    (h : DivTwoPow k ((b : ℤ) • C)) : DivTwoPow k C := by
  obtain ⟨D, hD⟩ := h
  have hcop : IsCoprime ((2 : ℤ) ^ k) (b : ℤ) := by
    apply IsCoprime.pow_left
    obtain ⟨m, hm⟩ := hb
    exact ⟨-(m : ℤ), 1, by rw [hm]; push_cast; ring⟩
  have hdvd : ∀ i j, (2 ^ k : ℤ) ∣ C i j := by
    intro i j
    have h1 : (2 ^ k : ℤ) ∣ (b : ℤ) * C i j := ⟨D i j, by
      have := congrFun (congrFun hD i) j
      simpa [Matrix.smul_apply, smul_eq_mul] using this⟩
    exact hcop.dvd_of_dvd_mul_left h1
  choose E hE using hdvd
  exact ⟨Matrix.of E, by ext i j; simp [hE i j]⟩

theorem eq_one_of_modFour_of_pow_odd {X : Matrix n n ℤ} (hX : DivTwoPow 2 (X - 1)) {b : ℕ}
    (hb : Odd b) (hpow : X ^ b = 1) : X = 1 := by
  suffices h : ∀ k, 2 ≤ k → DivTwoPow k (X - 1) by
    have := eq_zero_of_forall_divTwoPow fun k => (h (k + 2) (by omega)).mono (by omega)
    exact sub_eq_zero.1 this
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hX
  | succ k hk ih =>
    obtain ⟨C, hC⟩ := ih
    set Y := X - 1 with hY
    have hgeom : ∀ j : ℕ, X ^ j = 1 + Y * ∑ i ∈ Finset.range j, X ^ i := by
      intro j
      rw [hY, mul_geom_sum]
      abel
    set Z := ∑ j ∈ Finset.range b, ∑ i ∈ Finset.range j, X ^ i with hZdef
    have hsum : ∑ j ∈ Finset.range b, X ^ j = (b : ℤ) • 1 + Y * Z := by
      rw [Finset.sum_congr rfl fun j _ => hgeom j, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, ← Finset.mul_sum, natCast_zsmul]
    have h0 : Y * ((b : ℤ) • 1 + Y * Z) = 0 := by
      rw [← hsum, hY, mul_geom_sum, hpow, sub_self]
    have h1 : (b : ℤ) • Y = -(Y * Y * Z) := by
      rw [mul_add, mul_smul_comm, mul_one, ← mul_assoc] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have h2 : DivTwoPow (2 * k) ((b : ℤ) • Y) := by
      rw [h1, hC]
      refine ⟨-(C * C * Z), ?_⟩
      rw [show (2 : ℤ) ^ (2 * k) = 2 ^ k * 2 ^ k by ring]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_neg]
    have h3 : DivTwoPow (2 * k) Y := divTwoPow_of_odd_smul hb h2
    exact h3.mono (by omega)

theorem eq_one_of_modFour_of_sq_eq_one {X : Matrix n n ℤ} (hX : DivTwoPow 2 (X - 1))
    (hsq : X * X = 1) : X = 1 := by
  suffices h : ∀ k, 2 ≤ k → DivTwoPow k (X - 1) by
    have := eq_zero_of_forall_divTwoPow fun k => (h (k + 2) (by omega)).mono (by omega)
    exact sub_eq_zero.1 this
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hX
  | succ k hk ih =>
    obtain ⟨C, hC⟩ := ih
    set Y := X - 1 with hY
    have hX' : X = 1 + Y := by rw [hY]; abel
    have h1 : (2 : ℤ) • Y = -(Y * Y) := by
      have h := hsq
      rw [hX', add_mul, mul_add, mul_add, one_mul, mul_one, one_mul] at h
      have h0 : (2 : ℤ) • Y + Y * Y = 0 := by
        calc (2 : ℤ) • Y + Y * Y = (1 + Y + (Y + Y * Y)) - 1 := by rw [two_smul]; abel
          _ = 0 := by rw [h, sub_self]
      exact eq_neg_of_add_eq_zero_left h0
    have e1 : (2 : ℤ) • Y = -((2 : ℤ) ^ (2 * k) • (C * C)) := by
      rw [h1, hC, smul_mul_smul_comm, ← pow_add, ← two_mul]
    have e2 : (2 : ℤ) • ((2 : ℤ) ^ (2 * k - 1) • -(C * C)) = -((2 : ℤ) ^ (2 * k) • (C * C)) := by
      rw [smul_neg, smul_neg, smul_smul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)]
    have h3 : Y = (2 : ℤ) ^ (2 * k - 1) • -(C * C) :=
      smul_right_injective (Matrix n n ℤ) (two_ne_zero) (e1.trans e2.symm)
    exact DivTwoPow.mono (by omega) (show DivTwoPow (2 * k - 1) Y from ⟨-(C * C), h3⟩)

theorem divTwoPow_pow_sub_one {k : ℕ} {X : Matrix n n ℤ} (hX : DivTwoPow k (X - 1)) (j : ℕ) :
    DivTwoPow k (X ^ j - 1) := by
  obtain ⟨C, hC⟩ := hX
  refine ⟨C * ∑ i ∈ Finset.range j, X ^ i, ?_⟩
  rw [← mul_geom_sum, hC, smul_mul_assoc]

theorem eq_one_of_modFour_of_pow_two_pow {X : Matrix n n ℤ} (hX : DivTwoPow 2 (X - 1)) :
    ∀ a : ℕ, X ^ 2 ^ a = 1 → X = 1
  | 0, h => by simpa using h
  | a + 1, h => by
    apply eq_one_of_modFour_of_pow_two_pow hX a
    apply eq_one_of_modFour_of_sq_eq_one (divTwoPow_pow_sub_one hX _)
    rw [← pow_add, ← mul_two, ← pow_succ]
    exact h

theorem eq_one_of_modFour_of_pow_eq_one {X : Matrix n n ℤ} (hX : DivTwoPow 2 (X - 1)) {m : ℕ}
    (hm : 0 < m) (hpow : X ^ m = 1) : X = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have h1 : X ^ 2 ^ a = 1 := by
    apply eq_one_of_modFour_of_pow_odd (divTwoPow_pow_sub_one hX _) hb
    rw [← pow_mul, hpow]
  exact eq_one_of_modFour_of_pow_two_pow hX a h1

theorem sq_eq_one_of_modTwo_of_pow_eq_one {M : Matrix n n ℤ} (hM : DivTwoPow 1 (M - 1)) {m : ℕ}
    (hm : 0 < m) (hpow : M ^ m = 1) : M ^ 2 = 1 := by
  obtain ⟨A, hA⟩ := hM
  have h4 : DivTwoPow 2 (M ^ 2 - 1) := by
    refine ⟨A + A * A, ?_⟩
    have hM' : M = 1 + (2 : ℤ) • A := by rw [← pow_one (2 : ℤ), ← hA]; abel
    rw [hM', sq, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
    rw [show (2 : ℤ) ^ 2 = 2 * 2 by norm_num, smul_add, ← smul_smul, ← smul_smul]
    rw [show (2 : ℤ) • (2 : ℤ) • A = (2 : ℤ) • A + (2 : ℤ) • A by rw [two_smul (R := ℤ) ((2 : ℤ) • A)]]
    abel
  refine eq_one_of_modFour_of_pow_eq_one h4 hm ?_
  rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]

end CFSG.Monster.B
