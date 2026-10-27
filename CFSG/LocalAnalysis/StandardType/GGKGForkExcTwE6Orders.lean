module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame

public section

namespace CFSG.StandardType

namespace ExcTwE6Nons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private def ggKGTo_A (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
    (q ^ 2 - 1)

private theorem ggKGTo_q_sub_one_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) : padicValNat p (q - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h2 : p ∣ 2 := by
    have := Nat.dvd_sub hpq h
    rwa [show q + 1 - (q - 1) = 2 by omega] at this
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  omega

private theorem ggKGTo_q2_sub_one_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) : padicValNat p (q ^ 2 - 1) = padicValNat p (q + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_le : p ≤ q + 1 := Nat.le_of_dvd (by omega) hpq
  have hq1 : q + 1 ≠ 0 := by omega
  have hqm : q - 1 ≠ 0 := by omega
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using Nat.sq_sub_sq q 1
  rw [hsq, padicValNat.mul hq1 hqm, ggKGTo_q_sub_one_val hp hp5 hq hpq, add_zero]

private theorem ggKGTo_odd_pow_add_one_val {p q n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q + 1) (hn : Odd n) :
    padicValNat p (q ^ n + 1) = padicValNat p (q + 1) + padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hpq h
      rwa [show q + 1 - q = 1 by omega] at this
    exact hp.not_dvd_one h1
  have h := padicValNat.pow_add_pow (p := p) (x := q) (y := 1) hpodd hpq hp_not_dvd_q hn
  simpa using h

private theorem ggKGTo_even_pow_sub_one_val {p q m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 ≤ q) (hpq : p ∣ q + 1) (hm : m ≠ 0) :
    padicValNat p ((q ^ 2) ^ m - 1) = padicValNat p (q + 1) + padicValNat p m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hpq h
      rwa [show q + 1 - q = 1 by omega] at this
    exact hp.not_dvd_one h1
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega : 0 < q + 1) hpq
    omega
  have hq2gt : 1 < q ^ 2 := by nlinarith
  have h2dvd : p ∣ q ^ 2 - 1 := by
    have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
    rw [hsq]
    exact dvd_mul_of_dvd_left hpq _
  have h2not : ¬ p ∣ q ^ 2 := fun h => hp_not_dvd_q (hp.dvd_of_dvd_pow h)
  have h := padicValNat.pow_sub_pow (p := p) (x := q ^ 2) (y := 1) hpodd hq2gt h2dvd h2not hm
  rw [ggKGTo_q2_sub_one_val hp hp5 hq hpq] at h
  simpa using h

private theorem ggKGTo_prod_val {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) :
    padicValNat p (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 + 1) * (q ^ 2 - 1))
      = padicValNat p (q ^ 36) + padicValNat p (q ^ 12 - 1) + padicValNat p (q ^ 9 + 1)
        + padicValNat p (q ^ 8 - 1) + padicValNat p (q ^ 6 - 1) + padicValNat p (q ^ 5 + 1)
        + padicValNat p (q ^ 2 - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h36 : q ^ 36 ≠ 0 := by positivity
  have h12 : q ^ 12 - 1 ≠ 0 := by
    have h : 1 < q ^ 12 := Nat.one_lt_pow (by norm_num) (by omega : 1 < q)
    omega
  have h9 : q ^ 9 + 1 ≠ 0 := by positivity
  have h8 : q ^ 8 - 1 ≠ 0 := by
    have h : 1 < q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega : 1 < q)
    omega
  have h6 : q ^ 6 - 1 ≠ 0 := by
    have h : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num) (by omega : 1 < q)
    omega
  have h5 : q ^ 5 + 1 ≠ 0 := by positivity
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have h : 1 < q ^ 2 := by nlinarith
    omega
  have n1 : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h36 h12) h9) h8) h6) h5
  have n2 : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h36 h12) h9) h8) h6
  have n3 : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h36 h12) h9) h8
  have n4 : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h36 h12) h9
  have n5 : q ^ 36 * (q ^ 12 - 1) ≠ 0 := mul_ne_zero h36 h12
  rw [padicValNat.mul n1 h2, padicValNat.mul n2 h5, padicValNat.mul n3 h6,
      padicValNat.mul n4 h8, padicValNat.mul n5 h9, padicValNat.mul h36 h12]

private theorem ggKGTo_A_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) :
    padicValNat p (ggKGTo_A q) = 6 * padicValNat p (q + 1) + padicValNat p 51840 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_le : p ≤ q + 1 := Nat.le_of_dvd (by omega) hpq
  have hq2 : 2 ≤ q := by omega
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro h
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hpq h
      rwa [show q + 1 - q = 1 by omega] at this
    exact hp.not_dvd_one h1
  have hp_not_dvd_2 : ¬ p ∣ 2 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    omega
  have hp_not_dvd_3 : ¬ p ∣ 3 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  have h36 : padicValNat p (q ^ 36) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hp_not_dvd_q]
  have h2 : padicValNat p (q ^ 2 - 1) = padicValNat p (q + 1) :=
    ggKGTo_q2_sub_one_val hp hp5 hq hpq
  have h12 : padicValNat p (q ^ 12 - 1) = padicValNat p (q + 1) + padicValNat p 6 := by
    have h := ggKGTo_even_pow_sub_one_val (p := p) (q := q) (m := 6) hp hp5 hq hpq (by norm_num)
    rwa [show (q ^ 2) ^ 6 = q ^ 12 by rw [← pow_mul]] at h
  have h8 : padicValNat p (q ^ 8 - 1) = padicValNat p (q + 1) + padicValNat p 4 := by
    have h := ggKGTo_even_pow_sub_one_val (p := p) (q := q) (m := 4) hp hp5 hq hpq (by norm_num)
    rwa [show (q ^ 2) ^ 4 = q ^ 8 by rw [← pow_mul]] at h
  have h6 : padicValNat p (q ^ 6 - 1) = padicValNat p (q + 1) + padicValNat p 3 := by
    have h := ggKGTo_even_pow_sub_one_val (p := p) (q := q) (m := 3) hp hp5 hq hpq (by norm_num)
    rwa [show (q ^ 2) ^ 3 = q ^ 6 by rw [← pow_mul]] at h
  have h9 : padicValNat p (q ^ 9 + 1) = padicValNat p (q + 1) + padicValNat p 9 :=
    ggKGTo_odd_pow_add_one_val hp hp5 hpq (by norm_num)
  have h5 : padicValNat p (q ^ 5 + 1) = padicValNat p (q + 1) + padicValNat p 5 :=
    ggKGTo_odd_pow_add_one_val hp hp5 hpq (by norm_num)
  have h6v : padicValNat p 6 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h23 : p ∣ 2 * 3 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h23 with h2' | h3'
    · exact hp_not_dvd_2 h2'
    · exact hp_not_dvd_3 h3'
  have h9v : padicValNat p 9 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h32 : p ∣ 3 ^ 2 := by simpa using h
    exact hp_not_dvd_3 (hp.dvd_of_dvd_pow h32)
  have h4v : padicValNat p 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h22 : p ∣ 2 ^ 2 := by simpa using h
    exact hp_not_dvd_2 (hp.dvd_of_dvd_pow h22)
  have h3v : padicValNat p 3 = 0 := padicValNat.eq_zero_of_not_dvd hp_not_dvd_3
  have h51840 : padicValNat p 51840 = padicValNat p 5 := by
    rw [show (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.pow, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd hp_not_dvd_2,
      padicValNat.eq_zero_of_not_dvd hp_not_dvd_3]
    ring
  rw [ggKGTo_A, ggKGTo_prod_val hp hq2, h36, h12, h9, h8, h6, h5, h2, h6v, h9v, h4v, h3v, h51840]
  ring

private theorem ggKGTo_ordTwistedE6_val {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 ≤ q) (hpq : p ∣ q + 1) :
    padicValNat p (ordTwistedE6 q) = 6 * padicValNat p (q + 1) + padicValNat p 51840 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_3 : ¬ p ∣ 3 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  have hg3 : Nat.gcd 3 (q + 1) ∣ 3 := Nat.gcd_dvd_left 3 (q + 1)
  have hpg : ¬ p ∣ Nat.gcd 3 (q + 1) := fun h => hp_not_dvd_3 (dvd_trans h hg3)
  have hcop : Nat.Coprime p (Nat.gcd 3 (q + 1)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpg
  have hgdvd : Nat.gcd 3 (q + 1) ∣ ggKGTo_A q := by
    have h1 : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right 3 (q + 1)
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
      exact dvd_mul_right (q + 1) (q - 1)
    have h3 : q ^ 2 - 1 ∣ ggKGTo_A q := by
      unfold ggKGTo_A
      exact dvd_mul_left (q ^ 2 - 1) _
    exact dvd_trans (dvd_trans h1 h2) h3
  have hord : ordTwistedE6 q = ggKGTo_A q / Nat.gcd 3 (q + 1) := rfl
  rw [hord, padicValNat.div' hcop hgdvd]
  exact ggKGTo_A_val hp hp5 hq hpq

theorem padicValNat_card_twE6_nonsplit
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1) :
    padicValNat p (Nat.card (twistedE6RootGroup K σ)) =
      6 * padicValNat p (2 ^ n + 1) + padicValNat p 51840 := by
  have hn : 1 ≤ n := by
    have hle : p ≤ 2 ^ n + 1 := Nat.le_of_dvd (by positivity) hpq
    have h2n : 4 ≤ 2 ^ n := by omega
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at h2n
    norm_num at h2n
  have hcard : Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (2 ^ n) :=
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (p := 2) (f := n) Nat.prime_two hn hK
      σ.toRingHom (by simpa using hσ)
  rw [hcard]
  exact ggKGTo_ordTwistedE6_val hp hp5 Nat.one_le_two_pow hpq

end ExcTwE6Nons

end CFSG.StandardType

end
