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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_ActTrivial_fermat (x : ℤ) : x ^ 3 ≡ x [ZMOD 3] := by
  have h : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  unfold Int.ModEq
  rcases h with h | h | h <;> simp [pow_succ, Int.mul_emod, h]

theorem aux_ActTrivial_fermat_iter (x : ℤ) (k : ℕ) : x ^ 3 ^ k ≡ x [ZMOD 3] := by
  induction k with
  | zero => simp [Int.ModEq]
  | succ k ih =>
    rw [show (3 : ℕ) ^ (k + 1) = 3 ^ k * 3 from pow_succ 3 k, pow_mul]
    exact (Int.ModEq.pow 3 ih).trans (aux_ActTrivial_fermat x)

theorem conj_eq_of_three_power_order {G : Type*} [Group G] (s c d : G)
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1) (hc3 : c ^ 3 = 1) (hcd : c * d = d * c)
    (hcd' : c ∉ Subgroup.zpowers d) (hsd : s * d * s⁻¹ ∈ Subgroup.zpowers d)
    (hsc : s * c * s⁻¹ ∈ Subgroup.closure ({c, d} : Set G)) :
    ∃ j : ℤ, s * c * s⁻¹ = c * d ^ j := by
  have hcomm : Commute c d := hcd
  have hform : ∀ x ∈ Subgroup.closure ({c, d} : Set G), ∃ i j : ℤ, x = c ^ i * d ^ j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨k, l, rfl⟩ := hy
      refine ⟨i + k, j + l, ?_⟩
      have hdc : d ^ j * c ^ k = c ^ k * d ^ j := ((hcomm.zpow_zpow k j).eq).symm
      calc c ^ i * d ^ j * (c ^ k * d ^ l) = c ^ i * (d ^ j * c ^ k) * d ^ l := by
            simp only [mul_assoc]
        _ = c ^ i * (c ^ k * d ^ j) * d ^ l := by rw [hdc]
        _ = c ^ (i + k) * d ^ (j + l) := by
            rw [zpow_add c i k, zpow_add d j l]
            simp only [mul_assoc]
    | inv x _ hx =>
      obtain ⟨i, j, rfl⟩ := hx
      refine ⟨-i, -j, ?_⟩
      rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
      exact ((hcomm.zpow_zpow (-i) (-j)).eq).symm
  obtain ⟨i, j0, hij⟩ := hform _ hsc
  obtain ⟨δ, hδ⟩ := Subgroup.mem_zpowers_iff.mp hsd
  have hconj : ∀ n m : ℤ, s * (c ^ n * d ^ m) * s⁻¹ = (s * c * s⁻¹) ^ n * (s * d * s⁻¹) ^ m := by
    intro n m
    rw [conj_zpow, conj_zpow]
    group
  have hpow : ∀ n : ℕ, ∃ j : ℤ, s ^ n * c * (s ^ n)⁻¹ = c ^ (i ^ n) * d ^ j := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨j', hj'⟩ := ih
      refine ⟨j0 * i ^ n + δ * j', ?_⟩
      have h1 : s ^ (n + 1) * c * (s ^ (n + 1))⁻¹ = s * (s ^ n * c * (s ^ n)⁻¹) * s⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        simp only [mul_assoc]
      rw [h1, hj', hconj, hij, ← hδ, (hcomm.zpow_zpow i j0).mul_zpow, ← zpow_mul, ← zpow_mul,
        ← zpow_mul, mul_assoc, ← zpow_add, pow_succ']
  obtain ⟨k, hk⟩ := hs
  obtain ⟨jk, hjk⟩ := hpow (3 ^ k)
  rw [hk, inv_one, mul_one, one_mul] at hjk
  have hcx : Commute (c ^ (i ^ 3 ^ k)) (d ^ jk) := hcomm.zpow_zpow _ _
  have hdiv : c ^ (1 - i ^ 3 ^ k) = d ^ jk := by
    rw [zpow_sub, zpow_one]
    calc c * (c ^ (i ^ 3 ^ k))⁻¹ = (c ^ (i ^ 3 ^ k) * d ^ jk) * (c ^ (i ^ 3 ^ k))⁻¹ := by
          rw [← hjk]
      _ = d ^ jk * c ^ (i ^ 3 ^ k) * (c ^ (i ^ 3 ^ k))⁻¹ := by rw [← hcx.eq]
      _ = d ^ jk := by rw [mul_inv_cancel_right]
  have hmem : c ^ (1 - i ^ 3 ^ k) ∈ Subgroup.zpowers d := by
    rw [hdiv]
    exact Subgroup.mem_zpowers_iff.mpr ⟨jk, rfl⟩
  have hc3z : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  have hdvd : ∀ m : ℤ, c ^ m ∈ Subgroup.zpowers d → (3 : ℤ) ∣ m := by
    intro m hm
    rw [zpow_eq_zpow_emod m hc3z] at hm
    have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hr with h | h | h
    · omega
    · rw [h, zpow_one] at hm
      exact absurd hm hcd'
    · rw [h] at hm
      have h4 : c = c ^ (2 : ℤ) * c ^ (2 : ℤ) := by
        rw [← zpow_add, show (2 : ℤ) + 2 = 1 + 3 by norm_num, zpow_add, hc3z, zpow_one, mul_one]
      exfalso
      apply hcd'
      rw [h4]
      exact mul_mem hm hm
  have hm3 := hdvd _ hmem
  have hF : i ^ 3 ^ k % 3 = i % 3 := aux_ActTrivial_fermat_iter i k
  have hi1 : i % 3 = 1 := by
    generalize i ^ 3 ^ k = X at hm3 hF
    omega
  have hci : c ^ i = c := by
    rw [zpow_eq_zpow_emod i hc3z, hi1, zpow_one]
  refine ⟨j0, ?_⟩
  rw [hij, hci]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
