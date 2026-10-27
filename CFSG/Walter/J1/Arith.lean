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

namespace CFSG.Walter.J1

theorem arith_e0 {J I b0 b3 c m d : ℕ} (hd : d = 1 ∨ d = 3)
    (hJ : J = 7 + (c + 168 * m) + 3 * b3 + 168)
    (hI : I = 1 + b0 + (c + 168 * m) + b3 + 28)
    (h3 : 3 * b3 + 168 = 168 * d) (hc : 2 * c + 112 = 112 * d)
    (hG : 120 * J = 168 * I) (h5 : J % 5 = d % 5) :
    J = 511 ∨ J = 623 := by
  rcases hd with rfl | rfl
  · have hm : m ≤ 2 := by omega
    interval_cases m <;> omega
  · have hm : m ≤ 4 := by omega
    interval_cases m <;> omega

theorem arith_e1 {J I b0 b3 b7 c m r : ℕ}
    (hJ : J = 7 + (c + 168 * m) + 3 * b3 + 168 + 7 * b7)
    (hI : I = 1 + b0 + (c + 168 * m) + b3 + 28 + b7)
    (h3 : 3 * b3 + 168 = 168 * 3) (h7 : 7 * b7 = 8 * r) (hc : 2 * c + 112 + 112 = 112 * 3)
    (hG : 120 * J = 168 * I) :
    J = 567 + 168 * m + 8 * r ∧ 7 * b0 + 336 * m = 1456 + 32 * r := by
  constructor <;> omega

theorem arith_r7 {J b0 m : ℕ} (hJ : J = 567 + 168 * m + 8 * 7)
    (hb0 : 7 * b0 + 336 * m = 1456 + 32 * 7) (h5 : J % 5 = 3) :
    J = 623 ∨ J = 1463 := by
  have hm : m ≤ 5 := by omega
  interval_cases m <;> omega

theorem arith_index {a m b0 J k I : ℕ} (ha7 : 7 ∣ a) (ha : a ≠ 7) (hac : Nat.Coprime a 30)
    (hJ : J = 567 + 168 * m + 8 * a) (hb0 : 7 * b0 + 336 * m = 1456 + 32 * a)
    (hG : 120 * J = a * k * I) (hI : a ∣ I - 1) (hk : k ∣ 120) (hk2 : 2 ∣ k) : False := by
  obtain ⟨a', rfl⟩ := ha7
  have hc : Nat.Coprime a' 30 := Nat.Coprime.coprime_dvd_left (Dvd.intro_left 7 rfl) hac
  have h2 : ¬ 2 ∣ a' := fun h0 => by
    have := Nat.dvd_gcd h0 (by norm_num : 2 ∣ 30); rw [hc] at this; norm_num at this
  have h3 : ¬ 3 ∣ a' := fun h0 => by
    have := Nat.dvd_gcd h0 (by norm_num : 3 ∣ 30); rw [hc] at this; norm_num at this
  have h5 : ¬ 5 ∣ a' := fun h0 => by
    have := Nat.dvd_gcd h0 (by norm_num : 5 ∣ 30); rw [hc] at this; norm_num at this
  have ha'7 : 7 ≤ a' := by
    by_contra h0
    push Not at h0
    interval_cases a' <;> omega
  obtain ⟨k', hkk'⟩ := hk
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hk'60 : k' ∣ 60 := by
    obtain ⟨k'', rfl⟩ := hk2
    exact ⟨k'', by linarith⟩
  have hmain : k' * (81 + 24 * m + 8 * a') = a' * I := by
    rw [hJ] at hG
    have : k * (k' * (81 + 24 * m + 8 * a')) = k * (a' * I) := by
      have h1 : k * k' = 120 := hkk'.symm
      calc k * (k' * (81 + 24 * m + 8 * a')) = (k * k') * (81 + 24 * m + 8 * a') := by ring
        _ = 120 * (81 + 24 * m + 8 * a') := by rw [h1]
        _ = k * (a' * I) := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) this
  have hc60 : Nat.Coprime a' 60 := by
    have : (60 : ℕ) = 2 * 30 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 30) hc) hc
  have hcop : Nat.Coprime a' k' := Nat.Coprime.coprime_dvd_right hk'60 hc60
  have hdvd : a' ∣ 81 + 24 * m := by
    have h1 : a' ∣ k' * (81 + 24 * m + 8 * a') := ⟨I, hmain⟩
    have h2 := hcop.dvd_of_dvd_mul_left h1
    exact (Nat.dvd_add_right (dvd_mul_left a' 8)).mp (by rwa [add_comm] at h2)
  obtain ⟨q, hq⟩ := hdvd
  have hIq : I = k' * (q + 8) := by
    have : a' * I = a' * (k' * (q + 8)) := by rw [← hmain, hq]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [hIq] at hI
  have hM : a' ∣ (k' * (q + 8) - 1) / 7 := Nat.dvd_div_of_mul_dvd hI
  have hq42 : q ≤ 42 := by
    by_contra hq43
    push Not at hq43
    have : a' * 43 ≤ a' * q := Nat.mul_le_mul_left a' hq43
    omega
  have hk'mem : k' ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hk'60, by norm_num⟩
  have : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
  rw [this] at hk'mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk'mem
  have h7 : 7 ∣ k' * (q + 8) - 1 := Nat.dvd_trans (Dvd.intro a' rfl) hI
  rcases hk'mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases q <;> (try omega) <;>
    (norm_num at hM; have hle := Nat.le_of_dvd (by norm_num) hM; interval_cases a' <;> omega)

theorem false_of_card_sylow {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {p M : ℕ}
    [hp : Fact p.Prime] (hG : Nat.card G = p * M) (hpM : ¬ p ∣ M) (hM : 1 < M)
    (hdiv : ∀ d ∈ Nat.divisors M, d % p = 1 → d = 1) : False := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hpp : p.Prime := hp.out
  have hP : Nat.card P = p := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have h1 : p ^ k ∣ p * M := by rw [← hk, ← hG]; exact Subgroup.card_subgroup_dvd_card _
    have h2 : p ∣ p ^ k := by
      rw [← hk]
      have := Sylow.pow_dvd_card_of_pow_dvd_card P (n := 1) (by rw [hG]; simp)
      simpa using this
    rw [hk]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp at h2; exact absurd h2 hpp.one_lt.ne'
      · simp
    · exfalso
      have h3 : p * p ∣ p * M := by
        have := (pow_dvd_pow p hk2).trans h1
        rwa [pow_two] at this
      exact hpM (Nat.dvd_of_mul_dvd_mul_left hpp.pos h3)
  have hidx : (P : Subgroup G).index = M := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hG] at this
    exact Nat.eq_of_mul_eq_mul_left hpp.pos this
  have hn := card_sylow_modEq_one p G
  have hnd := Sylow.card_dvd_index P
  rw [hidx] at hnd
  have hn1 : Nat.card (Sylow p G) = 1 := by
    refine hdiv _ (Nat.mem_divisors.mpr ⟨hnd, by omega⟩) ?_
    unfold Nat.ModEq at hn
    rw [hn, Nat.one_mod_eq_one.mpr hpp.one_lt.ne']
  have : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hn1).1
  have hN := Sylow.normal_of_subsingleton P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) with h0 | h0
  · rw [h0, Subgroup.card_bot] at hP
    exact hpp.one_lt.ne hP
  · rw [h0, Subgroup.card_top, hG] at hP
    have : p * M = p * 1 := by rw [hP, mul_one]
    have := Nat.eq_of_mul_eq_mul_left hpp.pos this
    omega

theorem divisors_840_73 : ∀ d ∈ Nat.divisors 840, d % 73 = 1 → d = 1 := by decide +kernel

theorem divisors_840_89 : ∀ d ∈ Nat.divisors 840, d % 89 = 1 → d = 1 := by decide +kernel

end CFSG.Walter.J1
