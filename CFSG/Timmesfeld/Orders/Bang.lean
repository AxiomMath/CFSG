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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Polynomial

namespace CFSG.Timmesfeld

@[expose] def IsPrimitivePrimeDivisor (p k : ℕ) : Prop :=
  p.Prime ∧ p ∣ 2 ^ k - 1 ∧ ∀ j : ℕ, 0 < j → j < k → ¬ p ∣ 2 ^ j - 1

namespace Bang

theorem dvd_two_pow_sub_one_iff {p : ℕ} (k : ℕ) : p ∣ 2 ^ k - 1 ↔ (2 : ZMod p) ^ k = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
  simp

theorem isRoot_of_dvd {n p : ℕ} (h : p ∣ ((cyclotomic n ℤ).eval 2).natAbs) :
    (cyclotomic n (ZMod p)).IsRoot 2 := by
  have he := cyclotomic.eval_apply (2 : ℤ) n (Int.castRingHom (ZMod p))
  simp only [map_ofNat] at he
  rw [IsRoot.def, he, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.mpr h

theorem orderOf_eq_of_dvd {n p : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0)
    (h : p ∣ ((cyclotomic n ℤ).eval 2).natAbs) :
    ∃ a m : ℕ, ¬ p ∣ m ∧ n = p ^ a * m ∧ orderOf (2 : ZMod p) = m := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  refine ⟨a, m, hm, rfl, ?_⟩
  have : NeZero (m : ZMod p) := ⟨by rwa [Ne, ZMod.natCast_eq_zero_iff]⟩
  exact (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp (isRoot_of_dvd h)).eq_orderOf.symm

theorem primitive_of_orderOf {n p : ℕ} (h : orderOf (2 : ZMod p) = n) :
    p ∣ 2 ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ 2 ^ k - 1 := by
  refine ⟨(dvd_two_pow_sub_one_iff n).mpr (h ▸ pow_orderOf_eq_one _), fun k hk hkn hpk => ?_⟩
  have := orderOf_dvd_of_pow_eq_one ((dvd_two_pow_sub_one_iff k).mp hpk)
  rw [h] at this
  exact absurd (Nat.le_of_dvd hk this) (not_le.mpr hkn)

theorem two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h2
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem padicValNat_le_one {n p a m : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (ha : 0 < a)
    (hn : n = p ^ a * m) (hm : orderOf (2 : ZMod p) = m) (hm0 : 0 < m) :
    padicValNat p ((cyclotomic n ℤ).eval 2).natAbs ≤ 1 := by
  set d := p ^ (a - 1) * m with hd_def
  have hnd : n = d * p := by
    rw [hn, hd_def, mul_right_comm, ← pow_succ, Nat.sub_add_cancel ha]
  have hd0 : 0 < d := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hm0.ne')
  have hdn : d ∈ n.properDivisors := by
    rw [Nat.mem_properDivisors, hnd]
    exact ⟨dvd_mul_right d p, lt_mul_right hd0 hp.out.one_lt⟩
  have heval := eval_dvd (x := (2 : ℤ))
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdn)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at heval
  have hnat : (2 ^ d - 1) * ((cyclotomic n ℤ).eval 2).natAbs ∣ 2 ^ n - 1 := by
    have h := Int.natAbs_dvd_natAbs.mpr heval
    rw [Int.natAbs_mul] at h
    have h1 : ((2 : ℤ) ^ d - 1).natAbs = 2 ^ d - 1 := by
      have : ((2 : ℤ) ^ d - 1) = ((2 ^ d - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub Nat.one_le_two_pow]; simp
      rw [this, Int.natAbs_natCast]
    have h2 : ((2 : ℤ) ^ n - 1).natAbs = 2 ^ n - 1 := by
      have : ((2 : ℤ) ^ n - 1) = ((2 ^ n - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub Nat.one_le_two_pow]; simp
      rw [this, Int.natAbs_natCast]
    rwa [h1, h2] at h
  have hlte : padicValNat p (2 ^ n - 1) = padicValNat p (2 ^ d - 1) + 1 := by
    have h1 : 1 < 2 ^ d := Nat.one_lt_two_pow hd0.ne'
    have h2 : p ∣ 2 ^ d - 1 :=
      (dvd_two_pow_sub_one_iff d).mpr (orderOf_dvd_iff_pow_eq_one.mp (hm ▸ dvd_mul_left m _))
    have h3 : ¬ p ∣ 2 ^ d := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h))
    have := padicValNat.pow_sub_pow (p := p) (x := 2 ^ d) (y := 1)
      (hp.out.odd_of_ne_two hp2) h1 (by simpa using h2) h3 (n := p) hp.out.ne_zero
    rwa [one_pow, ← pow_mul, ← hnd, padicValNat_self] at this
  have hΦ0 : ((cyclotomic n ℤ).eval 2).natAbs ≠ 0 := by
    intro h0
    have := hnat
    rw [h0, mul_zero, zero_dvd_iff] at this
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by rw [hnd]; exact (mul_pos hd0 hp.out.pos).ne')
    omega
  have hd1 : 2 ^ d - 1 ≠ 0 := by
    have : 1 < 2 ^ d := Nat.one_lt_two_pow hd0.ne'
    omega
  have hn1 : 2 ^ n - 1 ≠ 0 := by
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by rw [hnd]; exact (mul_pos hd0 hp.out.pos).ne')
    omega
  have hle := (padicValNat_dvd_iff_le (p := p) hn1).mp (pow_padicValNat_dvd.trans hnat)
  rw [padicValNat.mul hd1 hΦ0, hlte] at hle
  omega

theorem three_mul_le_two_pow_sub_one {p : ℕ} (hp : 5 ≤ p) : 3 * p ≤ 2 ^ p - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  have h := (Nat.lt_two_pow_self (n := k))
  rw [pow_add]
  omega

theorem lt_natAbs_cyclotomic_eval {n p a m : ℕ} (hp : p.Prime) (ha : 0 < a) (hpm : ¬ p ∣ m)
    (hn : n = p ^ a * m) (hm2 : 2 ≤ m) (hmp : m ∣ p - 1) (h6 : n ≠ 6) :
    p < ((cyclotomic n ℤ).eval 2).natAbs := by
  have hp1 := hp.one_lt
  have hmle : m ≤ p - 1 := Nat.le_of_dvd (by omega) hmp
  rcases Nat.lt_or_ge 1 a with ha2 | ha1
  ·
    set N := p ^ (a - 1) * m with hN
    have hnN : n = N * p := by
      rw [hn, hN, mul_right_comm, ← pow_succ, Nat.sub_add_cancel ha]
    have hpN : p ∣ N := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m
    have hN1 : 1 < N := by
      have : p ≤ p ^ (a - 1) := Nat.le_self_pow (by omega) p
      have : p ≤ N := this.trans (Nat.le_mul_of_pos_right _ (by omega))
      omega
    have hexp := cyclotomic_expand_eq_cyclotomic hp hpN ℤ
    have heval : (cyclotomic n ℤ).eval 2 = (cyclotomic N ℤ).eval ((2 ^ p : ℕ) : ℤ) := by
      rw [hnN, ← hexp, expand_eval]; push_cast; rfl
    have hlow := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (q := 2 ^ p) hN1
      (Nat.one_lt_two_pow hp.ne_zero).ne'
    rw [← heval] at hlow
    have h1 : 2 ^ p - 1 ≤ (2 ^ p - 1) ^ N.totient :=
      Nat.le_self_pow (Nat.totient_pos.mpr (by omega)).ne' _
    have h2 : p ≤ 2 ^ p - 1 := by have := Nat.lt_two_pow_self (n := p); omega
    omega
  ·
    have ha1 : a = 1 := by omega
    subst ha1
    rw [pow_one] at hn
    have hexp := cyclotomic_expand_eq_cyclotomic_mul hp hpm ℤ
    have heval : (cyclotomic m ℤ).eval ((2 ^ p : ℕ) : ℤ) =
        (cyclotomic n ℤ).eval 2 * (cyclotomic m ℤ).eval 2 := by
      have := congrArg (eval (2 : ℤ)) hexp
      rw [expand_eval, eval_mul, mul_comm m p, ← hn] at this
      push_cast; exact this
    have hlow := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (q := 2 ^ p) (by omega : 1 < m)
      (Nat.one_lt_two_pow hp.ne_zero).ne'
    rw [heval, Int.natAbs_mul] at hlow
    have hup : ((cyclotomic m ℤ).eval 2).natAbs ≤ 2 ^ m - 1 := by
      have hdvd := eval_dvd (x := (2 : ℤ)) (cyclotomic.dvd_X_pow_sub_one m ℤ)
      simp only [eval_sub, eval_pow, eval_X, eval_one] at hdvd
      have h := Int.natAbs_dvd_natAbs.mpr hdvd
      have h2 : ((2 : ℤ) ^ m - 1).natAbs = 2 ^ m - 1 := by
        have : ((2 : ℤ) ^ m - 1) = ((2 ^ m - 1 : ℕ) : ℤ) := by
          rw [Nat.cast_sub Nat.one_le_two_pow]; simp
        rw [this, Int.natAbs_natCast]
      rw [h2] at h
      exact Nat.le_of_dvd (by have := Nat.one_lt_two_pow (n := m) (by omega); omega) h
    by_contra hle
    push Not at hle
    have hkey : (2 ^ p - 1) ^ m.totient < p * (2 ^ m - 1) :=
      hlow.trans_le (Nat.mul_le_mul hle hup)
    have hpow : 2 ^ m ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) hmle
    have hpp : 2 ^ p = 2 * 2 ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    have hpl : p ≤ 2 ^ (p - 1) := by
      have := Nat.lt_two_pow_self (n := p - 1); omega
    rcases Nat.lt_or_ge m.totient 2 with ht | ht
    ·
      have ht1 : m.totient = 1 := by
        have := Nat.totient_pos.mpr (by omega : 0 < m); omega
      have hm2' : m = 2 := by
        rcases Nat.totient_eq_one_iff.mp ht1 with h | h <;> omega
      subst hm2'
      rw [ht1, pow_one] at hkey
      have hp5 : p < 5 := by
        by_contra h5
        have := three_mul_le_two_pow_sub_one (p := p) (by omega)
        norm_num at hkey
        omega
      have hp3 : p = 3 := by
        interval_cases p <;> simp_all (config := { decide := true })
      exact h6 (by rw [hn, hp3])
    · have h2 : (2 ^ p - 1) ^ 2 ≤ (2 ^ p - 1) ^ m.totient :=
        Nat.pow_le_pow_right (by omega) ht
      have h3 : p * 2 ^ (p - 1) ≤ (2 ^ p - 1) ^ 2 := by
        rw [sq]
        apply Nat.mul_le_mul <;> omega
      have h4 : p * (2 ^ m - 1) < p * 2 ^ (p - 1) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by omega)
        omega
      omega

end Bang

open Bang in
theorem exists_primitive_prime_dvd_two_pow_sub_one (n : ℕ) (hn : 2 ≤ n) (h6 : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ 2 ^ k - 1 := by
  set Φ := ((cyclotomic n ℤ).eval 2).natAbs with hΦ
  have hΦ1 : 1 < Φ := by
    simpa using sub_one_lt_natAbs_cyclotomic_eval (q := 2) (by omega : 1 < n) (by norm_num)
  by_contra hcon
  push Not at hcon
  have key : ∀ p, p.Prime → p ∣ Φ → ∃ a m, 0 < a ∧ ¬ p ∣ m ∧ n = p ^ a * m ∧
      orderOf (2 : ZMod p) = m ∧ p ≠ 2 ∧ 2 ≤ m ∧ m ∣ p - 1 := by
    intro p hp hpΦ
    have := Fact.mk hp
    obtain ⟨a, m, hm, hnm, hord⟩ := orderOf_eq_of_dvd (by omega) hpΦ
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h0 : (2 : ZMod 2) = 0 := rfl
      rw [h0, orderOf_eq_zero_iff.mpr] at hord
      · exact hm0 hord.symm
      · rw [isOfFinOrder_iff_pow_eq_one]
        rintro ⟨k, hk, hk1⟩
        rw [zero_pow hk.ne'] at hk1
        exact zero_ne_one hk1
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [orderOf_eq_one_iff] at hord
      have : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast hord
      rw [ZMod.natCast_eq_natCast_iff'] at this
      have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      have h2 : 2 % p = 2 := Nat.mod_eq_of_lt (by have := hp.two_le; omega)
      omega
    have hmdvd : m ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp2)
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, one_mul] at hnm
      subst hnm
      obtain ⟨h1, h2⟩ := primitive_of_orderOf hord
      obtain ⟨k, hk, hkn, hpk⟩ := hcon p hp h1
      exact absurd hpk (h2 k hk hkn)
    · exact ⟨a, m, ha, hm, hnm, hord, hp2, by omega, hmdvd⟩
  have hp : Φ.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨a, m, ha, hm, hnm, hord, hp2, hm2, hmp⟩ := key _ hp (Nat.minFac_dvd Φ)
  set p := Φ.minFac
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ Φ → q = p := by
    intro q hq hqΦ
    obtain ⟨a', m', ha', hm', hnm', hord', hq2, hm2', hmq⟩ := key q hq hqΦ
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
  have hv := padicValNat_le_one hp2 ha hnm hord (by omega)
  have hΦp : Φ = p := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : Φ ≠ 0)
      (fun hd hdΦ => huniq hd hdΦ)
    set k := Φ.primeFactorsList.length
    have hk : padicValNat p Φ = k := by rw [hpow]; exact padicValNat.prime_pow k
    have hk1 : k ≤ 1 := hk ▸ hv
    interval_cases k
    · rw [pow_zero] at hpow; omega
    · rwa [pow_one] at hpow
  have hlt := lt_natAbs_cyclotomic_eval hp ha hm hnm hm2 hmp h6
  rw [← hΦ, hΦp] at hlt
  exact lt_irrefl _ hlt

theorem exists_isPrimitivePrimeDivisor {k : ℕ} (hk : 2 ≤ k) (h6 : k ≠ 6) :
    ∃ p : ℕ, IsPrimitivePrimeDivisor p k :=
  exists_primitive_prime_dvd_two_pow_sub_one k hk h6

namespace IsPrimitivePrimeDivisor

variable {p k : ℕ}

theorem prime (h : IsPrimitivePrimeDivisor p k) : p.Prime := h.1

theorem dvd (h : IsPrimitivePrimeDivisor p k) : p ∣ 2 ^ k - 1 := h.2.1

theorem ne_two (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
  have h2 := Nat.dvd_sub h1 h.2.1
  rw [show 2 ^ k - (2 ^ k - 1) = 1 by have := Nat.one_le_two_pow (n := k); omega] at h2
  exact absurd h2 (by norm_num)

theorem dvd_sub_one_iff (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (a : ℕ) :
    p ∣ 2 ^ a - 1 ↔ k ∣ a := by
  constructor
  · intro ha
    have hg : p ∣ 2 ^ Nat.gcd a k - 1 := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one]
      exact Nat.dvd_gcd ha h.2.1
    by_contra hka
    have hlt : Nat.gcd a k < k := lt_of_le_of_ne (Nat.gcd_le_right _ hk)
      (fun he => hka (he ▸ Nat.gcd_dvd_left a k))
    exact h.2.2 _ (Nat.gcd_pos_of_pos_right _ hk) hlt hg
  · intro hka
    exact h.2.1.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hka)

theorem two_pow_two_mul_sub_one (a : ℕ) : 2 ^ (2 * a) - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
  zify [h1, h2]
  ring

theorem dvd_add_one_iff (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (a : ℕ) :
    p ∣ 2 ^ a + 1 ↔ k ∣ 2 * a ∧ ¬ k ∣ a := by
  have hp := h.1
  constructor
  · intro ha
    refine ⟨(h.dvd_sub_one_iff hk _).mp
      ((two_pow_two_mul_sub_one a).symm ▸ dvd_mul_of_dvd_right ha _), fun hka => ?_⟩
    have h1 := (h.dvd_sub_one_iff hk a).mpr hka
    have h2 := Nat.dvd_sub ha h1
    rw [show 2 ^ a + 1 - (2 ^ a - 1) = 2 by have := Nat.one_le_two_pow (n := a); omega] at h2
    exact h.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · rintro ⟨h2a, hna⟩
    have h1 := (h.dvd_sub_one_iff hk _).mpr h2a
    rw [two_pow_two_mul_sub_one] at h1
    rcases hp.dvd_mul.mp h1 with h1 | h1
    · exact absurd ((h.dvd_sub_one_iff hk a).mp h1) hna
    · exact h1

theorem eq_two_of_dvd_three (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (h3 : p ∣ 3) :
    k = 2 := by
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_three).mp h3
  have hk2 : k ∣ 2 := (h.dvd_sub_one_iff hk 2).mp (by rw [hp3]; norm_num)
  have hk1 : ¬ k ∣ 1 := fun h1 => by
    have := (h.dvd_sub_one_iff hk 1).mpr h1
    rw [hp3] at this
    norm_num at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h' | h'
  · exact absurd (h' ▸ dvd_refl k) hk1
  · exact h'

end IsPrimitivePrimeDivisor

end CFSG.Timmesfeld
