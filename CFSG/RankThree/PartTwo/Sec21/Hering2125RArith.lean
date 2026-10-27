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

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

theorem cubic_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have h2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (ha.trans hab.le)
  have hab' : (a : ℤ) + 1 ≤ b := by exact_mod_cast hab
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  zify [h1, h2]
  nlinarith [mul_pos (show (0 : ℤ) < b - a by linarith) (show (0 : ℤ) < b ^ 2 + a * b + a ^ 2 - 1
    by nlinarith)]

theorem cubic_injective {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (cubic_strictMono ha hab).ne
  · exact hab
  · exact absurd h.symm (cubic_strictMono hb hab).ne

theorem sl2_card_odd {p k n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (hn : 2 ≤ n)
    (h : p ^ k * ((p ^ k) ^ 2 - 1) = 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1))) :
    p = 5 ∧ k = 1 ∧ n = 2 := by
  set u := p ^ k with hu
  set m := 2 ^ n with hm
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmeven : 2 ∣ m := dvd_pow_self 2 (by omega)
  have hu1 : 1 ≤ u := Nat.one_le_pow _ _ hp.pos
  have hcop : Nat.Coprime u (2 * m) := by
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have : Nat.Coprime u (2 ^ (n + 1)) := Nat.Coprime.pow k (n + 1) h2
    simpa [hm, pow_succ, mul_comm] using this
  have hdiv : u ∣ 2 * m * (m ^ 2 - 1) := by
    refine ⟨u ^ 2 - 1, ?_⟩
    have : u * (u ^ 2 - 1) = 2 * m * (m ^ 2 - 1) := by rw [h]; ring
    exact this.symm
  have hu_dvd : u ∣ m ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdiv
  have hsq : m ^ 2 - 1 = (m - 1) * (m + 1) := by
    have : 1 ≤ m := by omega
    zify [Nat.one_le_pow 2 m this, this]
    ring
  rw [hsq] at hu_dvd
  have hpdvd : p ∣ (m - 1) * (m + 1) := (dvd_pow_self p (by omega)).trans hu_dvd
  have hp_ndvd_two : ¬ p ∣ 2 := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hle : u ≤ m + 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpdvd with hd | hd
    · have hcp : Nat.Coprime (p ^ k) (m + 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd'
        apply hp_ndvd_two
        have : m + 1 - (m - 1) = 2 := by omega
        rw [← this]
        exact Nat.dvd_sub hd' hd
      have := hcp.dvd_of_dvd_mul_right hu_dvd
      have := Nat.le_of_dvd (by omega) this
      omega
    · have hcp : Nat.Coprime (p ^ k) (m - 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd'
        apply hp_ndvd_two
        have : m + 1 - (m - 1) = 2 := by omega
        rw [← this]
        exact Nat.dvd_sub hd hd'
      have := hcp.dvd_of_dvd_mul_left hu_dvd
      have := Nat.le_of_dvd (by omega) this
      omega
  have hm_le : m ≤ 4 := by
    by_contra hcon
    have hm5 : 5 ≤ m := by omega
    have h1 : u * (u ^ 2 - 1) ≤ (m + 1) * ((m + 1) ^ 2 - 1) := by
      rcases hle.lt_or_eq with hlt | heq
      · exact (cubic_strictMono hu1 hlt).le
      · rw [heq]
    have hm1 : 1 ≤ m := by omega
    have h2 : (m + 1) * ((m + 1) ^ 2 - 1) = m * (m + 1) * (m + 2) := by
      have : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this]
      ring
    have h3 : 2 * (m * (m ^ 2 - 1)) = 2 * m * (m - 1) * (m + 1) := by
      have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm1
      zify [this, hm1]
      ring
    rw [h, h2, h3] at h1
    have : 2 * (m - 1) ≤ m + 2 := by
      have hpos : 0 < m * (m + 1) := by positivity
      have h4 : (m * (m + 1)) * (2 * (m - 1)) ≤ (m * (m + 1)) * (m + 2) := by
        calc (m * (m + 1)) * (2 * (m - 1)) = 2 * m * (m - 1) * (m + 1) := by ring
          _ ≤ m * (m + 1) * (m + 2) := h1
      exact Nat.le_of_mul_le_mul_left h4 hpos
    omega
  have hm4' : m = 4 := le_antisymm hm_le hm4
  have hn2 : n = 2 := by
    have : 2 ^ n = 2 ^ 2 := by rw [← hm, hm4']; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  have hu5 : u = 5 := by
    rw [hm4'] at h
    have hu_le : u ≤ 5 := by omega
    interval_cases u <;> omega
  have hp5 : p = 5 := by
    have : p ∣ 5 := by
      rw [← hu5]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp this
  refine ⟨hp5, ?_, hn2⟩
  have h5k : p ^ k = 5 ^ 1 := by rw [← hu, hu5]; norm_num
  rw [hp5] at h5k
  exact Nat.pow_right_injective (by norm_num) h5k

theorem sl2_card_cases {p k n T : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hn : 2 ≤ n)
    (hT : T = 1 ∨ T = 2)
    (h : p ^ k * ((p ^ k) ^ 2 - 1) = T * (2 ^ n * ((2 ^ n) ^ 2 - 1))) :
    (p = 2 ∧ k = n ∧ T = 1) ∨ (p = 5 ∧ k = 1 ∧ n = 2 ∧ T = 2) := by
  have hm4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm1 : 1 ≤ 2 ^ n := by omega
  have hu1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  by_cases hp2 : p = 2
  · subst hp2
    rcases hT with rfl | rfl
    · rw [one_mul] at h
      have := cubic_injective hu1 hm1 h
      exact Or.inl ⟨rfl, Nat.pow_right_injective (le_refl 2) this, rfl⟩
    · exfalso
      by_cases hkn : k ≤ n
      · have h1 : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hkn
        have h2 : 2 ^ k * ((2 ^ k) ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          rcases h1.lt_or_eq with hlt | heq
          · exact (cubic_strictMono hu1 hlt).le
          · rw [heq]
        have h3 : 0 < 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          have : 1 < (2 ^ n) ^ 2 := by nlinarith
          exact Nat.mul_pos (by omega) (by omega)
        omega
      · have h1 : 2 * 2 ^ n ≤ 2 ^ k := by
          calc 2 * 2 ^ n = 2 ^ (n + 1) := by ring
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : (2 * 2 ^ n) * ((2 * 2 ^ n) ^ 2 - 1) ≤ 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
          rcases h1.lt_or_eq with hlt | heq
          · exact (cubic_strictMono (by omega) hlt).le
          · rw [← heq]
        have h3 : 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) < (2 * 2 ^ n) * ((2 * 2 ^ n) ^ 2 - 1) := by
          generalize 2 ^ n = m at hm4 hm1 ⊢
          have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm1
          have hm3 : 1 ≤ (2 * m) ^ 2 := Nat.one_le_pow _ _ (by omega)
          zify [hm2, hm3]
          nlinarith [mul_pos (show (0 : ℤ) < m by exact_mod_cast hm1)
            (show (0 : ℤ) < m ^ 2 by positivity)]
        omega
  · rcases hT with rfl | rfl
    · exfalso
      rw [one_mul] at h
      have hu1' : 1 ≤ p ^ k := hu1
      have := cubic_injective hu1' hm1 h
      have hp_odd : Odd p := hp.odd_of_ne_two hp2
      have hodd : Odd (p ^ k) := hp_odd.pow
      have heven : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
      rw [this] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    · obtain ⟨h5, hk1, hn2⟩ := sl2_card_odd hp hp2 hk hn h
      exact Or.inr ⟨h5, hk1, hn2, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
