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

theorem comm_pow3_of_normalizes {G : Type*} [Group G] (x r f : G)
    (hx27 : x ^ 27 = 1) (hx9 : x ^ 9 ≠ 1) (hr : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hrx : r * x * r⁻¹ ∈ Subgroup.zpowers x) (hr9 : r * x ^ 9 = x ^ 9 * r)
    (hrf : r ^ 3 = f) (hfx : f * x ≠ x * f) :
    r * x * r⁻¹ * x⁻¹ ∈ Subgroup.zpowers (x ^ 3) ∧
    r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹ ∈ Subgroup.zpowers (x ^ 9) ∧
    r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹ ≠ 1 := by
  have hord : orderOf x = 27 := by
    have h : orderOf x = 3 ^ (2 + 1) :=
      orderOf_eq_prime_pow (by norm_num; exact hx9) (by norm_num; exact hx27)
    norm_num at h
    exact h
  obtain ⟨L, hL⟩ := Subgroup.mem_zpowers_iff.1 hrx
  have hconj : ∀ n : ℕ, r ^ n * x * (r ^ n)⁻¹ = x ^ (L ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hsplit : r ^ (n + 1) * x * (r ^ (n + 1))⁻¹
          = r * (r ^ n * x * (r ^ n)⁻¹) * r⁻¹ := by
        simp only [pow_succ', mul_inv_rev, mul_assoc]
      rw [hsplit, ih, ← conj_zpow, ← hL, ← zpow_mul, pow_succ']
  obtain ⟨k, hk⟩ := hr
  have hfix : x ^ (L ^ 3 ^ k) = x := by
    have h := hconj (3 ^ k)
    rw [hk, one_mul, inv_one, mul_one] at h
    exact h.symm
  have hdiv27 : (27 : ℤ) ∣ L ^ 3 ^ k - 1 := by
    have h1 : x ^ (L ^ 3 ^ k - 1) = 1 := by
      rw [zpow_sub_one, hfix, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hord] at h2
    exact_mod_cast h2
  have hmod : (L : ZMod 3) ^ 3 ^ k = (L : ZMod 3) := ZMod.pow_card_pow _
  have hdiv3 : (3 : ℤ) ∣ L - 1 := by
    have h3 : ((3 : ℕ) : ℤ) ∣ L ^ 3 ^ k - 1 := dvd_trans (by norm_num) hdiv27
    have h5 : ((L ^ 3 ^ k - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 h3
    have h6 : ((L - 1 : ℤ) : ZMod 3) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5 - hmod
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h6
  obtain ⟨t, ht⟩ := hdiv3
  have e1 : r * x * r⁻¹ * x⁻¹ = x ^ (L - 1) := by
    rw [zpow_sub_one, ← hL]
  have h3c : r * x ^ 3 * r⁻¹ = (x ^ L) ^ 3 := by
    rw [hL, conj_pow]
  have e2 : r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹ = x ^ (3 * (L - 1)) := by
    rw [h3c]
    group
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, ht]
    refine Subgroup.mem_zpowers_iff.2 ⟨t, ?_⟩
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  · rw [e2, ht]
    refine Subgroup.mem_zpowers_iff.2 ⟨t, ?_⟩
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  · intro h
    rw [e2] at h
    have h27' : (27 : ℤ) ∣ 3 * (L - 1) := by
      have h4 := orderOf_dvd_iff_zpow_eq_one.2 h
      rw [hord] at h4
      exact_mod_cast h4
    have h9 : (9 : ℤ) ∣ L - 1 := by omega
    obtain ⟨s, hs⟩ := h9
    have hL9 : L = 1 + 9 * s := by linarith
    have hcube : L ^ 3 = 1 + 27 * (s + 9 * s ^ 2 + 27 * s ^ 3) := by
      rw [hL9]
      ring
    have hx27z : x ^ (27 : ℤ) = 1 := by
      rw [zpow_ofNat]
      exact hx27
    have hr3 : r ^ 3 * x * (r ^ 3)⁻¹ = x := by
      rw [hconj 3, hcube, zpow_add, zpow_one, zpow_mul, hx27z, one_zpow, mul_one]
    have hc : x * r ^ 3 = r ^ 3 * x := by
      calc x * r ^ 3 = (r ^ 3 * x * (r ^ 3)⁻¹) * r ^ 3 := by rw [hr3]
        _ = r ^ 3 * x := by group
    apply hfx
    rw [← hrf]
    exact hc.symm

theorem not_commute_of_mem_closure_pair {G : Type*} [Group G] (a c d x f : G) (i j m : ℤ)
    (hf : f = a ^ i * c ^ j) (hi : ¬ (3 : ℤ) ∣ i)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hm : ¬ (3 : ℤ) ∣ m)
    (hxc : x * c = c * x) (hxd : x * d = d * x) (had : a * d = d * a) (hcd : c * d = d * c)
    (hac : a * c = c * a) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : f * x ≠ x * f := by
  intro h
  have hxf : x * f * x⁻¹ = f := by
    rw [← h, mul_inv_cancel_right]
  have hcomm_ad : Commute a d := had
  have hcomm_da : Commute d a := hcomm_ad.symm
  have hxa' : x * a ^ i * x⁻¹ = (d ^ m * a) ^ i := by
    rw [← hxa, conj_zpow]
  have hxc' : x * c ^ j * x⁻¹ = c ^ j := by
    have hxc_comm : Commute x c := hxc
    rw [(hxc_comm.zpow_right j).eq, mul_inv_cancel_right]
  have hsplit : x * f * x⁻¹ = (x * a ^ i * x⁻¹) * (x * c ^ j * x⁻¹) := by
    rw [hf]
    group
  have h1 : x * f * x⁻¹ = d ^ (m * i) * f := by
    rw [hsplit, hxa', hxc', (hcomm_da.zpow_left m).mul_zpow, ← zpow_mul, hf, mul_assoc]
  have h2 : d ^ (m * i) = 1 := by
    have hf' : d ^ (m * i) * f = 1 * f := by
      rw [← h1, hxf, one_mul]
    exact mul_right_cancel hf'
  have h3 : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h4 : (3 : ℤ) ∣ m * i := by
    have h5 := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [h3] at h5
    exact_mod_cast h5
  rcases Int.prime_three.dvd_or_dvd h4 with h6 | h6
  · exact hm h6
  · exact hi h6


end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
