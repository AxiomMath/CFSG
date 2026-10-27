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

namespace CFSG.Quasithin.RonanE114

theorem geom_sum_odd {p f : ℕ} (hp : Odd p) (hf : Odd f) :
    Odd (∑ i ∈ Finset.range f, p ^ i) := by
  have h : ∀ n : ℕ, (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, Nat.odd_iff.mp hp]
      simp only [one_pow]
      omega
  exact Nat.odd_iff.mpr (by rw [h f]; exact Nat.odd_iff.mp hf)

theorem pow_eq_nine_of_pow_sub_one_eq_two_pow {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hk : p ^ f - 1 = 2 ^ k) : p ^ f = 9 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases Nat.even_or_odd f with ⟨g, hg⟩ | hfodd
  · have hg1 : 1 ≤ g := by omega
    set a := p ^ g with ha
    have ha3 : 3 ≤ a := le_trans hp3 (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ g := Nat.pow_le_pow_right hp.pos hg1)
    have hfa : p ^ f = a * a := by rw [hg, ← two_mul, pow_mul', sq]
    have hmul : (a - 1) * (a + 1) = 2 ^ k := by
      rw [← hk, hfa]
      have : a * a - 1 = (a - 1) * (a + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.sub_mul, Nat.one_mul]
        have : a ≤ a * a := Nat.le_mul_self a
        omega
      exact this.symm
    obtain ⟨i, hi, hia⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show a - 1 ∣ 2 ^ k from ⟨a + 1, hmul.symm⟩)
    obtain ⟨j, hj, hja⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show a + 1 ∣ 2 ^ k from ⟨a - 1, by rw [← hmul, mul_comm]⟩)
    have hi1 : 1 ≤ i := by
      by_contra h
      obtain rfl : i = 0 := by omega
      simp at hia
      omega
    have hj2 : 2 ≤ j := by
      by_contra h
      have h1 : j ≤ 1 := by omega
      have : 2 ^ j ≤ 2 := by
        calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 := by norm_num
      omega
    have hi_eq : i = 1 := by
      by_contra h
      have hi2 : 2 ≤ i := by omega
      have h4a : 4 ∣ 2 ^ i := by
        have : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 hi2
        simpa using this
      have h4b : 4 ∣ 2 ^ j := by
        have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj2
        simpa using this
      have h4 : 4 ∣ 2 ^ j - 2 ^ i := Nat.dvd_sub h4b h4a
      have h2 : 2 ^ j - 2 ^ i = 2 := by omega
      rw [h2] at h4
      omega
    subst hi_eq
    have : a = 3 := by omega
    rw [hfa, this]
  · have hf3 : 3 ≤ f := by
      rcases hfodd with ⟨m, hm⟩
      omega
    have hS : Odd (∑ i ∈ Finset.range f, p ^ i) := geom_sum_odd hpodd hfodd
    set S := ∑ i ∈ Finset.range f, p ^ i with hSdef
    have hdvd : p - 1 ∣ p ^ f - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow p 1 f
    have hmul : S * (p - 1) = p ^ f - 1 := by
      rw [hSdef, Nat.geomSum_eq (by omega) f]
      exact Nat.div_mul_cancel hdvd
    have hSd : S ∣ 2 ^ k := by
      rw [← hk, ← hmul]
      exact dvd_mul_right S _
    obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hSd
    have hi0 : i = 0 := by
      by_contra h
      have : 2 ∣ S := by
        rw [hiS]
        exact dvd_pow_self 2 h
      exact (Nat.not_even_iff_odd.mpr hS) (even_iff_two_dvd.mpr this)
    rw [hi0, pow_zero] at hiS
    rw [hiS, one_mul] at hmul
    have hpf : p ^ f = p := by
      have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
      omega
    have : p ^ f > p := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ f := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega

theorem exists_odd_prime_dvd_half_pred {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (h9 : p ^ f ≠ 9) (h4 : p ^ f % 4 = 1) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ (p ^ f - 1) / 2 := by
  by_contra hno
  push Not at hno
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hpos : (p ^ f - 1) / 2 ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := 2) (fun {d} hd hdd => by
    by_contra h
    exact hno d hd h hdd)
  set k := ((p ^ f - 1) / 2).primeFactorsList.length with hk
  have h2 : p ^ f - 1 = 2 ^ (k + 1) := by
    rw [pow_succ, ← hpow]
    omega
  exact h9 (pow_eq_nine_of_pow_sub_one_eq_two_pow hp hp2 hf h2)

theorem exists_odd_cofactor_add {p : ℕ} (hp : Odd p) :
    ∀ g : ℕ, ∃ S : ℤ, ((p : ℤ) ^ (2 * g + 1) + 1 = ((p : ℤ) + 1) * S) ∧ Odd S := by
  intro g
  induction g with
  | zero => exact ⟨1, by ring, odd_one⟩
  | succ g ih =>
    obtain ⟨S, hS, hSodd⟩ := ih
    have hpz : Odd (p : ℤ) := by exact_mod_cast hp
    refine ⟨(p : ℤ) ^ 2 * S - ((p : ℤ) - 1), ?_, ?_⟩
    · have : (p : ℤ) ^ (2 * (g + 1) + 1) = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * g + 1) := by ring
      rw [this]
      linear_combination ((p : ℤ) ^ 2) * hS
    · exact Odd.sub_even ((hpz.pow).mul hSodd) (by simpa using hpz.sub_odd odd_one)

theorem exists_odd_prime_dvd_half_succ {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f)
    (hfodd : Odd f) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ (p ^ f + 1) / 2 := by
  by_contra hno
  push Not at hno
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpfodd : Odd (p ^ f) := hpodd.pow
  have hpos : (p ^ f + 1) / 2 ≠ 0 := by
    have : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := 2) (fun {d} hd hdd => by
    by_contra h
    exact hno d hd h hdd)
  set k := ((p ^ f + 1) / 2).primeFactorsList.length + 1 with hk
  have h2 : p ^ f + 1 = 2 ^ k := by
    rw [hk, pow_succ, ← hpow]
    obtain ⟨m, hm⟩ : Even (p ^ f + 1) := hpfodd.add_one
    omega
  obtain ⟨g, hg⟩ := hfodd
  obtain ⟨S, hS, hSodd⟩ := exists_odd_cofactor_add hpodd g
  have hpf : (p : ℤ) ^ f + 1 = 2 ^ k := by
    have : ((p ^ f + 1 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by rw [h2]
    simpa using this
  rw [hg] at hpf
  have hSd : S ∣ 2 ^ k := by
    refine ⟨(p : ℤ) + 1, ?_⟩
    rw [← hpf, hS]
    ring
  have hSpos : 0 < S := by
    have h1 : 0 < (p : ℤ) ^ (2 * g + 1) + 1 := by positivity
    rw [hS] at h1
    by_contra hS0
    have hS0' : S ≤ 0 := not_lt.mp hS0
    have hp1 : (0 : ℤ) < (p : ℤ) + 1 := by positivity
    nlinarith
  lift S to ℕ using hSpos.le with S'
  have hSd' : S' ∣ 2 ^ k := by exact_mod_cast hSd
  obtain ⟨i, hi, hiS⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hSd'
  have hi0 : i = 0 := by
    by_contra h
    have : 2 ∣ S' := by
      rw [hiS]
      exact dvd_pow_self 2 h
    have hSodd' : Odd S' := by exact_mod_cast hSodd
    exact (Nat.not_even_iff_odd.mpr hSodd') (even_iff_two_dvd.mpr this)
  rw [hi0, pow_zero] at hiS
  subst hiS
  have hpf' : (p : ℤ) ^ (2 * g + 1) = p := by
    have : ((p : ℤ) ^ (2 * g + 1) + 1 = (p + 1) * 1) := by exact_mod_cast hS
    linarith
  have : p ^ (2 * g + 1) = p := by exact_mod_cast hpf'
  have hg1 : 1 ≤ g := by omega
  have : p ^ (2 * g + 1) > p := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (2 * g + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end CFSG.Quasithin.RonanE114
