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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
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

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

theorem three_mul_le_two_pow {n : ℕ} (hn : 4 ≤ n) : 3 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem not_three_dvd_two_pow_add_one_of_even {n : ℕ} (hn : Even n) : ¬ 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide))
  have h2 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h2]
  intro hd
  have h0 : 4 ^ k + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.2 hd
  have h3 : 4 ^ k + 1 ≡ 1 + 1 [MOD 3] := Nat.ModEq.add_right 1 h
  have h4 : (0 : ℕ) ≡ 1 + 1 [MOD 3] := h0.symm.trans h3
  revert h4
  decide

theorem exists_prime_gt_three_dvd {n : ℕ} (h2 : 2 ≤ n) (h3 : n ≠ 3) :
    ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ 2 ^ n + 1 := by
  by_contra hno
  push Not at hno
  have hpos : 2 ^ n + 1 ≠ 0 := by positivity
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    intro h
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n + 1 → d = 3 := by
    intro d hd hdv
    have hd2 : d ≠ 2 := by rintro rfl; exact hodd hdv
    by_contra hd3
    have h4 : 3 < d := by
      have := hd.two_le
      omega
    exact hno d hd h4 hdv
  rcases Nat.even_or_odd n with he | ho
  · have hne : 2 ^ n + 1 ≠ 1 := by
      have : 0 < 2 ^ n := by positivity
      omega
    have hq := Nat.minFac_prime hne
    have := hall hq (Nat.minFac_dvd _)
    rw [this] at hq
    exact not_three_dvd_two_pow_add_one_of_even he (this ▸ Nat.minFac_dvd _)
  · have hn5 : 5 ≤ n := by
      rcases ho with ⟨k, rfl⟩
      omega
    have hpowe := Nat.eq_prime_pow_of_unique_prime_dvd hpos hall
    set k := (2 ^ n + 1).primeFactorsList.length with hk
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hlte := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide) (by decide)
      (by decide) ho
    have hv3 : padicValNat 3 (2 ^ n + 1) = k := by
      rw [hpowe, padicValNat.prime_pow]
    rw [one_pow] at hlte
    have hvv : padicValNat 3 (2 + 1) = 1 := by
      norm_num
    rw [hv3, hvv] at hlte
    have hdvd : 3 ^ padicValNat 3 n ∣ n := pow_padicValNat_dvd
    have hle : 3 ^ padicValNat 3 n ≤ n := Nat.le_of_dvd (by omega) hdvd
    have h5 : 2 ^ n + 1 ≤ 3 * n := by
      rw [hpowe, hlte, pow_add, pow_one]
      exact Nat.mul_le_mul_left 3 hle
    have := three_mul_le_two_pow (n := n) (by omega)
    omega

theorem prime_ne_two_three_of_dvd {r s : ℕ} (hr : r.Prime) (hs : Odd s) (h : r ∣ 2 ^ s - 1) :
    5 ≤ r := by
  obtain ⟨k, rfl⟩ := hs
  have h1 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  have h4pos : 0 < 4 ^ k := by positivity
  have h4 : ∃ c, 4 ^ k = 3 * c + 1 := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ 4 ^ k)).1
      (show 1 ≡ 4 ^ k [MOD 3] by
        simpa using (Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide)).symm)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by omega⟩
  obtain ⟨c, hc⟩ := h4
  rw [h1] at h
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    omega
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact absurd hr (by decide)
  have := hr.two_le
  omega

theorem not_dvd_two_pow_sub_one_self {r : ℕ} (hr : r.Prime) : ¬ r ∣ 2 ^ r - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro h
  have h1 : ((2 ^ r - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ZMod.pow_card] at h1
  have h2 : (1 : ZMod r) = 0 := by
    have : (2 : ZMod r) - 1 = 0 := h1
    have h3 : (2 : ZMod r) = 1 + 1 := by norm_num
    rw [h3] at this
    simpa using this
  exact one_ne_zero h2

theorem two_pow_add_one_dvd {r m : ℕ} (hr : Odd r) : 2 ^ m + 1 ∣ 2 ^ (r * m) + 1 := by
  have := Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 hr
  simpa [one_pow, ← pow_mul, mul_comm] using this

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
