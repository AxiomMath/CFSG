module

public import CFSG.Open.Defs
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.StandardType

open CFSG.Timmesfeld

private lemma l05nL4z_orderOf_eq {p k : ℕ} (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) :
    orderOf (2 : ZMod p) = k := by
  have hp : p.Prime := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : (2 : ZMod p) ^ k = 1 := (Bang.dvd_two_pow_sub_one_iff k).mp h.dvd
  have hdvd : orderOf (2 : ZMod p) ∣ k := orderOf_dvd_of_pow_eq_one hpow
  refine le_antisymm (Nat.le_of_dvd hk hdvd) ?_
  by_contra hle
  have hlt : orderOf (2 : ZMod p) < k := Nat.lt_of_not_le hle
  have hpos : 0 < orderOf (2 : ZMod p) := Nat.pos_of_dvd_of_pos hdvd hk
  exact h.2.2 _ hpos hlt
    ((Bang.dvd_two_pow_sub_one_iff (orderOf (2 : ZMod p))).mpr (pow_orderOf_eq_one _))

private lemma l05nL4z_ppd_dvd_sub_one {p k : ℕ} (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) :
    k ∣ p - 1 := by
  have hp : p.Prime := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : (2 : ZMod p) ≠ 0 := by
    intro h0
    exact h.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h0))
  have hd := ZMod.orderOf_dvd_card_sub_one hne
  rwa [l05nL4z_orderOf_eq h hk] at hd

private lemma l05nL4z_not_dvd_div {r a b : ℕ} (hb : b ∣ a) (h : ¬ r ∣ a) : ¬ r ∣ a / b :=
  fun hr => h (hr.trans (Nat.div_dvd_of_dvd hb))

private lemma l05nL4z_three_dvd_sq_sub_one (n : ℕ) : 3 ∣ ((2 : ℕ) ^ n) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (4 : ℕ) 1 n
  rw [show 4 - 1 = 3 by norm_num, one_pow] at h
  rw [show ((2 : ℕ) ^ n) ^ 2 = 4 ^ n by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    conv_lhs => rw [← pow_mul]
    conv_rhs => rw [← pow_mul]
    rw [Nat.mul_comm n 2]]
  exact h

private lemma l05nL4z_a_factor {r n d : ℕ} (hr : IsPrimitivePrimeDivisor r (10 * n))
    (hn : 0 < n) (hd : ¬ 10 ∣ d) : ¬ r ∣ ((2 : ℕ) ^ n) ^ d - 1 := by
  rw [← pow_mul, hr.dvd_sub_one_iff (by omega : 0 < 10 * n) (n * d)]
  rw [Nat.mul_comm 10 n, Nat.mul_dvd_mul_iff_left hn]
  exact hd

private lemma l05nL4z_b_factor_sub {r n d : ℕ} (hr : IsPrimitivePrimeDivisor r (5 * n))
    (hn : 0 < n) (hd : ¬ 5 ∣ d) : ¬ r ∣ ((2 : ℕ) ^ n) ^ d - 1 := by
  rw [← pow_mul, hr.dvd_sub_one_iff (by omega : 0 < 5 * n) (n * d)]
  rw [Nat.mul_comm 5 n, Nat.mul_dvd_mul_iff_left hn]
  exact hd

private lemma l05nL4z_b_factor_add {r n d : ℕ} (hr : IsPrimitivePrimeDivisor r (5 * n))
    (hn : 0 < n) (hd : ¬ 5 ∣ 2 * d) : ¬ r ∣ ((2 : ℕ) ^ n) ^ d + 1 := by
  rw [← pow_mul, hr.dvd_add_one_iff (by omega : 0 < 5 * n) (n * d)]
  intro hcon
  have h2 : ¬ 5 * n ∣ 2 * (n * d) := by
    rw [show 2 * (n * d) = n * (2 * d) by ring, Nat.mul_comm 5 n,
      Nat.mul_dvd_mul_iff_left hn]
    exact hd
  exact h2 hcon.1

private lemma l05nL4z_eleven_le {r n : ℕ} (hr : r.Prime) (hn : 1 ≤ n)
    (hdvd : 5 * n ∣ r - 1) : 11 ≤ r := by
  have hr2 : 2 ≤ r := hr.two_le
  rcases Nat.lt_or_ge 1 n with hn2 | hn1
  · have hle : 5 * n ≤ r - 1 := Nat.le_of_dvd (by omega) hdvd
    have h10 : 10 ≤ 5 * n := by omega
    omega
  · have hn1' : n = 1 := by omega
    subst hn1'
    have hr6 : 6 ≤ r := by
      have hle : 5 * 1 ≤ r - 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    by_contra hlt
    push Not at hlt
    interval_cases r <;>
      first
        | exact absurd hr (by decide)
        | exact absurd hdvd (by norm_num)

theorem ggResE6Dep_zsigmondy (n : ℕ) (hn : 1 ≤ n) :
    (∃ r : ℕ, r.Prime ∧ 11 ≤ r ∧ r ∣ 2 ^ (10 * n) - 1 ∧ ¬ r ∣ CFSG.Open.ordE6 (2 ^ n)) ∧
      (∃ r : ℕ, r.Prime ∧ 11 ≤ r ∧ r ∣ 2 ^ (5 * n) - 1 ∧
        ¬ r ∣ CFSG.Open.ordTwistedE6 (2 ^ n)) := by
  have hnpos : 0 < n := by omega
  constructor
  · obtain ⟨r, hr⟩ :=
      exists_isPrimitivePrimeDivisor (k := 10 * n) (by omega) (by omega)
    have hk10 : 0 < 10 * n := by omega
    have h11 : 11 ≤ r := by
      have hr2 : 2 ≤ r := hr.prime.two_le
      have hdvd := l05nL4z_ppd_dvd_sub_one hr hk10
      have hle : 10 * n ≤ r - 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    refine ⟨r, hr.prime, h11, hr.dvd, ?_⟩
    have h0 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 36 := by
      intro h
      have h1 : r ∣ (2 : ℕ) ^ n := hr.prime.dvd_of_dvd_pow h
      have h2 : r ∣ 2 := hr.prime.dvd_of_dvd_pow h1
      exact hr.ne_two hk10 ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp h2)
    have h12 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 12 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    have h9 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 9 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    have h8 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 8 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    have h6 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 6 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    have h5 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 5 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    have h2 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 2 - 1 := l05nL4z_a_factor hr hnpos (by norm_num)
    rw [CFSG.Open.ordE6]
    refine l05nL4z_not_dvd_div ?_ ?_
    · exact (Nat.gcd_dvd_left 3 ((2 : ℕ) ^ n - 1)).trans
        ((l05nL4z_three_dvd_sq_sub_one n).trans
          (dvd_mul_left (((2 : ℕ) ^ n) ^ 2 - 1) _))
    · exact Nat.Prime.not_dvd_mul hr.prime
        (Nat.Prime.not_dvd_mul hr.prime
          (Nat.Prime.not_dvd_mul hr.prime
            (Nat.Prime.not_dvd_mul hr.prime
              (Nat.Prime.not_dvd_mul hr.prime
                (Nat.Prime.not_dvd_mul hr.prime h0 h12) h9) h8) h6) h5) h2
  · obtain ⟨r, hr⟩ :=
      exists_isPrimitivePrimeDivisor (k := 5 * n) (by omega) (by omega)
    have hk5 : 0 < 5 * n := by omega
    have h11 : 11 ≤ r := l05nL4z_eleven_le hr.prime hn (l05nL4z_ppd_dvd_sub_one hr hk5)
    refine ⟨r, hr.prime, h11, hr.dvd, ?_⟩
    have h0 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 36 := by
      intro h
      have h1 : r ∣ (2 : ℕ) ^ n := hr.prime.dvd_of_dvd_pow h
      have h2 : r ∣ 2 := hr.prime.dvd_of_dvd_pow h1
      exact hr.ne_two hk5 ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp h2)
    have h12 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 12 - 1 := l05nL4z_b_factor_sub hr hnpos (by norm_num)
    have h9p : ¬ r ∣ ((2 : ℕ) ^ n) ^ 9 + 1 :=
      l05nL4z_b_factor_add hr hnpos (by norm_num : ¬ 5 ∣ 2 * 9)
    have h8 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 8 - 1 := l05nL4z_b_factor_sub hr hnpos (by norm_num)
    have h6 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 6 - 1 := l05nL4z_b_factor_sub hr hnpos (by norm_num)
    have h5p : ¬ r ∣ ((2 : ℕ) ^ n) ^ 5 + 1 := by
      rw [← pow_mul, hr.dvd_add_one_iff hk5 (n * 5)]
      intro hcon
      exact hcon.2 (by rw [Nat.mul_comm n 5])
    have h2 : ¬ r ∣ ((2 : ℕ) ^ n) ^ 2 - 1 := l05nL4z_b_factor_sub hr hnpos (by norm_num)
    rw [CFSG.Open.ordTwistedE6]
    refine l05nL4z_not_dvd_div ?_ ?_
    · exact (Nat.gcd_dvd_left 3 ((2 : ℕ) ^ n + 1)).trans
        ((l05nL4z_three_dvd_sq_sub_one n).trans
          (dvd_mul_left (((2 : ℕ) ^ n) ^ 2 - 1) _))
    · exact Nat.Prime.not_dvd_mul hr.prime
        (Nat.Prime.not_dvd_mul hr.prime
          (Nat.Prime.not_dvd_mul hr.prime
            (Nat.Prime.not_dvd_mul hr.prime
              (Nat.Prime.not_dvd_mul hr.prime
                (Nat.Prime.not_dvd_mul hr.prime h0 h12) h9p) h8) h6) h5p) h2

end CFSG.StandardType
