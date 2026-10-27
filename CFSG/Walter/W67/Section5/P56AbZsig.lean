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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open Polynomial

namespace CFSG.Walter.W67.P56Ab

theorem dvd_three_pow_sub_one_iff {p : ℕ} (k : ℕ) :
    p ∣ 3 ^ k - 1 ↔ (3 : ZMod p) ^ k = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), sub_eq_zero]
  simp

theorem dvd_three_pow_sub_one_iff_of_orderOf {v n : ℕ} (h : orderOf (3 : ZMod v) = n) (k : ℕ) :
    v ∣ 3 ^ k - 1 ↔ n ∣ k := by
  rw [dvd_three_pow_sub_one_iff, ← h, orderOf_dvd_iff_pow_eq_one]

theorem isRoot_of_dvd {n p : ℕ} (h : p ∣ ((cyclotomic n ℤ).eval 3).natAbs) :
    (cyclotomic n (ZMod p)).IsRoot 3 := by
  have he := cyclotomic.eval_apply (3 : ℤ) n (Int.castRingHom (ZMod p))
  simp only [map_ofNat] at he
  rw [IsRoot.def, he, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.mpr h

theorem orderOf_eq_of_dvd {n p : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0)
    (h : p ∣ ((cyclotomic n ℤ).eval 3).natAbs) :
    ∃ a m : ℕ, ¬ p ∣ m ∧ n = p ^ a * m ∧ orderOf (3 : ZMod p) = m := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  refine ⟨a, m, hm, rfl, ?_⟩
  have : NeZero (m : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp (isRoot_of_dvd h)).eq_orderOf.symm

theorem primitive_of_orderOf {n p : ℕ} (h : orderOf (3 : ZMod p) = n) :
    p ∣ 3 ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ 3 ^ k - 1 := by
  refine ⟨(dvd_three_pow_sub_one_iff n).mpr (h ▸ pow_orderOf_eq_one _), fun k hk hkn hpk => ?_⟩
  have := orderOf_dvd_of_pow_eq_one ((dvd_three_pow_sub_one_iff k).mp hpk)
  rw [h] at this
  exact absurd (Nat.le_of_dvd hk this) (not_le.mpr hkn)

theorem three_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h3
  have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp this)

theorem padicValNat_le_one {n p a m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (ha : 0 < a) (hn : n = p ^ a * m) (hm : orderOf (3 : ZMod p) = m) (hm0 : 0 < m) :
    padicValNat p ((cyclotomic n ℤ).eval 3).natAbs ≤ 1 := by
  set d := p ^ (a - 1) * m with hd_def
  have hnd : n = d * p := by
    rw [hn, hd_def, mul_right_comm, ← pow_succ, Nat.sub_add_cancel ha]
  have hd0 : 0 < d := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hm0.ne')
  have hdn : d ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors, hnd]
    exact ⟨dvd_mul_right d p, lt_mul_right hd0 hp.out.one_lt⟩
  have h3pow : ∀ k : ℕ, ((3 : ℤ) ^ k - 1).natAbs = 3 ^ k - 1 := by
    intro k
    have : ((3 : ℤ) ^ k - 1) = ((3 ^ k - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; simp
    rw [this, Int.natAbs_natCast]
  have heval := eval_dvd (x := (3 : ℤ))
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdn)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at heval
  have hnat : (3 ^ d - 1) * ((cyclotomic n ℤ).eval 3).natAbs ∣ 3 ^ n - 1 := by
    have h := Int.natAbs_dvd_natAbs.mpr heval
    rw [Int.natAbs_mul, h3pow, h3pow] at h
    exact h
  have hlte : padicValNat p (3 ^ n - 1) = padicValNat p (3 ^ d - 1) + 1 := by
    have h1 : 1 < 3 ^ d := Nat.one_lt_pow hd0.ne' (by norm_num)
    have h2 : p ∣ 3 ^ d - 1 :=
      (dvd_three_pow_sub_one_iff d).mpr (orderOf_dvd_iff_pow_eq_one.mp (hm ▸ dvd_mul_left m _))
    have h3 : ¬ p ∣ 3 ^ d := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp (hp.out.dvd_of_dvd_pow h))
    have := padicValNat.pow_sub_pow (p := p) (x := 3 ^ d) (y := 1)
      (hp.out.odd_of_ne_two hp2) h1 (by simpa using h2) h3 (n := p) hp.out.ne_zero
    rwa [one_pow, ← pow_mul, ← hnd, padicValNat_self] at this
  have hn1 : 3 ^ n - 1 ≠ 0 := by
    have : 1 < 3 ^ n := Nat.one_lt_pow (by rw [hnd]; exact (mul_pos hd0 hp.out.pos).ne')
      (by norm_num)
    omega
  have hΦ0 : ((cyclotomic n ℤ).eval 3).natAbs ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_dvd_iff] at hnat
    exact hn1 hnat
  have hd1 : 3 ^ d - 1 ≠ 0 := by
    have : 1 < 3 ^ d := Nat.one_lt_pow hd0.ne' (by norm_num)
    omega
  have hle := (padicValNat_dvd_iff_le (p := p) hn1).mp (pow_padicValNat_dvd.trans hnat)
  rw [padicValNat.mul hd1 hΦ0, hlte] at hle
  omega

theorem le_two_pow_pred (p : ℕ) : p ≤ 2 ^ (p - 1) := by
  rcases p with _ | p
  · simp
  · simpa using Nat.lt_two_pow_self (n := p)

theorem exists_orderOf_three_eq {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ v : ℕ, v.Prime ∧ orderOf (3 : ZMod v) = n := by
  set Φ := ((cyclotomic n ℤ).eval 3).natAbs with hΦ
  have hΦ1 : 1 < Φ := by
    have := sub_one_lt_natAbs_cyclotomic_eval (q := 3) (by omega : 1 < n) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    omega
  by_contra hcon
  push Not at hcon
  have key : ∀ p, p.Prime → p ∣ Φ → ∃ a m, 0 < a ∧ ¬ p ∣ m ∧ n = p ^ a * m ∧
      orderOf (3 : ZMod p) = m ∧ p ≠ 2 ∧ p ≠ 3 ∧ 2 ≤ m ∧ m ∣ p - 1 := by
    intro p hp hpΦ
    have := Fact.mk hp
    obtain ⟨a, m, hm, hnm, hord⟩ := orderOf_eq_of_dvd (by omega) hpΦ
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h0 : (3 : ZMod 3) = 0 := rfl
      rw [h0, orderOf_eq_zero_iff.mpr] at hord
      · exact hm0 hord.symm
      · rw [isOfFinOrder_iff_pow_eq_one]
        rintro ⟨k, hk, hk1⟩
        rw [zero_pow hk.ne'] at hk1
        exact zero_ne_one hk1
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [orderOf_eq_one_iff] at hord
      have : ((3 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast hord
      rw [ZMod.natCast_eq_natCast_iff'] at this
      have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      rcases Nat.lt_or_ge p 3 with hp3' | hp3'
      ·
        have hp2 : p = 2 := by have := hp.two_le; omega
        subst hp2
        rw [mul_one] at hnm
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · rw [pow_zero] at hnm; omega
        · rw [hnm] at hodd
          exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' ha.ne').mpr even_two)
      · have h3 : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
        omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      apply hm1
      rw [← hord]
      have h31 : (3 : ZMod 2) = 1 := rfl
      rw [h31, orderOf_one]
    have hmdvd : m ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one (three_ne_zero_zmod hp3)
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, one_mul] at hnm
      subst hnm
      exact absurd hord (hcon p hp)
    · exact ⟨a, m, ha, hm, hnm, hord, hp2, hp3, by omega, hmdvd⟩
  have hp : Φ.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨a, m, ha, hm, hnm, hord, hp2, hp3, hm2, hmp⟩ := key _ hp (Nat.minFac_dvd Φ)
  set p := Φ.minFac
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ Φ → q = p := by
    intro q hq hqΦ
    obtain ⟨a', m', ha', hm', hnm', hord', hq2, hq3, hm2', hmq⟩ := key q hq hqΦ
    by_contra hqp
    have hqm : q ∣ m := by
      have hqn : q ∣ n := hnm' ▸ dvd_mul_of_dvd_left (dvd_pow_self q ha'.ne') m'
      rw [hnm] at hqn
      rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)) hqp
      · exact h
    have hpm' : p ∣ m' := by
      have hpn : p ∣ n := hnm ▸ dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') m
      rw [hnm'] at hpn
      rcases (Nat.Prime.dvd_mul hp).mp hpn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm hqp
      · exact h
    have h1 : q ≤ m := Nat.le_of_dvd (by omega) hqm
    have h2 : m ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hmp
    have h3 : p ≤ m' := Nat.le_of_dvd (by omega) hpm'
    have h4 : m' ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hmq
    omega
  have := Fact.mk hp
  have hv := padicValNat_le_one hp2 hp3 ha hnm hord (by omega)
  have hΦp : Φ = p := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : Φ ≠ 0)
      (fun hd hdΦ => huniq hd hdΦ)
    set k := Φ.primeFactorsList.length
    have hk : padicValNat p Φ = k := by rw [hpow]; exact padicValNat.prime_pow k
    have hk1 : k ≤ 1 := hk ▸ hv
    interval_cases k
    · rw [pow_zero] at hpow; omega
    · rwa [pow_one] at hpow
  have hlow := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (q := 3) (by omega : 1 < n)
    (by norm_num)
  simp only [Nat.cast_ofNat] at hlow
  rw [← hΦ, hΦp] at hlow
  have hpn : p ∣ n := hnm ▸ dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') m
  have htot : p - 1 ≤ n.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hpn)
  have h2 : 2 ^ (p - 1) ≤ 2 ^ n.totient := Nat.pow_le_pow_right (by norm_num) htot
  have h3 := le_two_pow_pred p
  norm_num at hlow
  omega

theorem exists_primitive_prime_dvd_three_pow_sub_one {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ v : ℕ, v.Prime ∧ v ∣ 3 ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ v ∣ 3 ^ k - 1 := by
  obtain ⟨v, hv, hord⟩ := exists_orderOf_three_eq hn hodd
  exact ⟨v, hv, primitive_of_orderOf hord⟩

end CFSG.Walter.W67.P56Ab
