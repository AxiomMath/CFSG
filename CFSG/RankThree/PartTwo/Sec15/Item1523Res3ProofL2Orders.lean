module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1523Res3

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem padicValNat_two_pow_mul_odd (m : ℕ) {x : ℕ} (hx : Odd x) :
    padicValNat 2 (2 ^ m * x) = m := by
  rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hx.not_two_dvd_nat, add_zero]

theorem odd_pow_sub_one_of_even {t a : ℕ} (ht : Even t) (ht1 : 1 ≤ t) (ha : 1 ≤ a) :
    Odd (t ^ a - 1) := by
  have h2 : 2 ∣ t ^ a := dvd_pow (even_iff_two_dvd.mp ht) (by omega)
  have h1 : 1 ≤ t ^ a := Nat.one_le_pow _ _ (by omega)
  exact Nat.odd_iff.mpr (by omega)

theorem odd_pow_add_one_of_even {t a : ℕ} (ht : Even t) (ha : 1 ≤ a) : Odd (t ^ a + 1) := by
  have h2 : 2 ∣ t ^ a := dvd_pow (even_iff_two_dvd.mp ht) (by omega)
  exact Nat.odd_iff.mpr (by omega)

theorem odd_gcd_three (m : ℕ) : Odd (Nat.gcd 3 m) :=
  Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 m)

theorem two_pow_sq_sub_one_lt (n : ℕ) : (2 ^ n) ^ 2 - 1 < 2 ^ (2 * n) := by
  have h1 : 0 < 2 ^ (2 * n) := by positivity
  rw [← pow_mul, mul_comm n 2]
  omega

theorem not_cube_dvd_small {n q : ℕ} (hn : n = 4 ∨ n = 6 ∨ n = 8) (hq : 2 ≤ q) :
    ¬ q ^ 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have hcheck : ∀ r < 41, 2 ≤ r → ¬ r ^ 3 ∣ 255 ∧ ¬ r ^ 3 ∣ 4095 ∧ ¬ r ^ 3 ∣ 65535 := by
    decide
  intro hd
  have hM : (2 ^ n) ^ 2 - 1 ≤ 65535 := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hpos : 0 < (2 ^ n) ^ 2 - 1 := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hq41 : q < 41 := by
    by_contra h
    have h1 : 41 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp h) 3
    have h2 := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨h4, h6, h8⟩ := hcheck q hq41 hq
  rcases hn with rfl | rfl | rfl
  · exact h4 (by simpa using hd)
  · exact h6 (by simpa using hd)
  · exact h8 (by simpa using hd)

theorem false_of_sl3_two {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (H : 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 ^ k - 1) =
      (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1))) : False := by
  have ht2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hte : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  have hMo : Odd ((2 ^ n) ^ 2 - 1) :=
    odd_pow_sub_one_of_even ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow
      (by norm_num)
  have hXo : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1)) :=
    Nat.odd_mul.mpr ⟨odd_pow_sub_one_of_even hte (by omega) (by norm_num),
      odd_pow_sub_one_of_even hte (by omega) (by norm_num)⟩
  have hv : n = 3 * k := by
    have h := congrArg (padicValNat 2) H
    have e1 : padicValNat 2 (2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 ^ k - 1)) = n := by
      rw [mul_assoc]
      exact padicValNat_two_pow_mul_odd n (Nat.odd_mul.mpr ⟨hMo, odd_gcd_three _⟩)
    have e2 := padicValNat_two_pow_mul_odd (3 * k) hXo
    rw [pow_mul'] at e2
    rw [e1, e2] at h
    exact h
  set t := 2 ^ k with ht
  have h3 : 2 ^ n = t ^ 3 := by rw [hv, ht, ← pow_mul, mul_comm]
  have hMg : ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t - 1) = (t ^ 2 - 1) * (t ^ 3 - 1) := by
    have H2 : 2 ^ n * (((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t - 1)) =
        2 ^ n * ((t ^ 2 - 1) * (t ^ 3 - 1)) := by
      rw [← mul_assoc, H, h3]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) H2
  have hM6 : (2 ^ n) ^ 2 = t ^ 6 := by rw [h3, ← pow_mul]
  have hg1 : 1 ≤ Nat.gcd 3 (t - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : (2 ^ n) ^ 2 - 1 ≤ ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t - 1) :=
    Nat.le_mul_of_pos_right _ hg1
  have h5 : (t ^ 2 - 1) * (t ^ 3 - 1) < t ^ 5 := by
    have h2 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3' : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc (t ^ 2 - 1) * (t ^ 3 - 1) ≤ (t ^ 2 - 1) * t ^ 3 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < t ^ 2 * t ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = t ^ 5 := by ring
  have h6 : 2 * t ^ 5 ≤ t ^ 6 := by
    calc 2 * t ^ 5 ≤ t * t ^ 5 := Nat.mul_le_mul_right _ ht2
      _ = t ^ 6 := by ring
  have h51 : 1 ≤ t ^ 5 := Nat.one_le_pow _ _ (by omega)
  omega

theorem false_of_su3_two {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (H : 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 ^ k + 1) =
      (2 ^ k) ^ 3 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1))) : False := by
  have ht2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hte : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
  have hMo : Odd ((2 ^ n) ^ 2 - 1) :=
    odd_pow_sub_one_of_even ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow
      (by norm_num)
  have hXo : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1)) :=
    Nat.odd_mul.mpr ⟨odd_pow_sub_one_of_even hte (by omega) (by norm_num),
      odd_pow_add_one_of_even hte (by norm_num)⟩
  have hv : n = 3 * k := by
    have h := congrArg (padicValNat 2) H
    have e1 : padicValNat 2 (2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 ^ k + 1)) = n := by
      rw [mul_assoc]
      exact padicValNat_two_pow_mul_odd n (Nat.odd_mul.mpr ⟨hMo, odd_gcd_three _⟩)
    have e2 := padicValNat_two_pow_mul_odd (3 * k) hXo
    rw [pow_mul'] at e2
    rw [e1, e2] at h
    exact h
  set t := 2 ^ k with ht
  have h3 : 2 ^ n = t ^ 3 := by rw [hv, ht, ← pow_mul, mul_comm]
  have hMg : ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t + 1) = (t ^ 2 - 1) * (t ^ 3 + 1) := by
    have H2 : 2 ^ n * (((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t + 1)) =
        2 ^ n * ((t ^ 2 - 1) * (t ^ 3 + 1)) := by
      rw [← mul_assoc, H, h3]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) H2
  have hM6 : (2 ^ n) ^ 2 = t ^ 6 := by rw [h3, ← pow_mul]
  have hg1 : 1 ≤ Nat.gcd 3 (t + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : (2 ^ n) ^ 2 - 1 ≤ ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (t + 1) :=
    Nat.le_mul_of_pos_right _ hg1
  have h5 : (t ^ 2 - 1) * (t ^ 3 + 1) < t ^ 5 + t ^ 2 := by
    have h2 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc (t ^ 2 - 1) * (t ^ 3 + 1) < t ^ 2 * (t ^ 3 + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = t ^ 5 + t ^ 2 := by ring
  have h6 : 2 * t ^ 5 ≤ t ^ 6 := by
    calc 2 * t ^ 5 ≤ t * t ^ 5 := Nat.mul_le_mul_right _ ht2
      _ = t ^ 6 := by ring
  have h52 : t ^ 2 + 1 ≤ t ^ 5 := by
    have : t ^ 2 * 4 ≤ t ^ 2 * t ^ 3 := Nat.mul_le_mul_left _ (by
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ t ^ 3 := Nat.pow_le_pow_left ht2 3)
    have h2 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc t ^ 2 + 1 ≤ t ^ 2 * 4 := by omega
      _ ≤ t ^ 2 * t ^ 3 := this
      _ = t ^ 5 := by ring
  omega

theorem pos_of_two_pow_sq_sub_one {n : ℕ} (hn : 1 ≤ n) : 0 < (2 ^ n) ^ 2 - 1 := by
  have : 2 ≤ (2 ^ n) ^ 2 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ n) ^ 2 := by rw [pow_mul]
  omega

theorem odd_two_pow_sq_sub_one (n : ℕ) (hn : 1 ≤ n) : Odd ((2 ^ n) ^ 2 - 1) :=
  odd_pow_sub_one_of_even ((Nat.even_pow' (by omega)).mpr even_two) Nat.one_le_two_pow
    (by norm_num)

theorem cube_dvd_of_odd {n q g : ℕ} (hq : Odd q) (hg : Nat.Coprime q g)
    (H : q ^ 3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) * g) : q ^ 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have hcop2 : Nat.Coprime (q ^ 3) (2 ^ n) :=
    Nat.Coprime.pow 3 n (Nat.coprime_two_right.mpr hq)
  have hcopg : Nat.Coprime (q ^ 3) g := Nat.Coprime.pow_left 3 hg
  rw [mul_assoc] at H
  exact hcopg.dvd_of_dvd_mul_right (hcop2.dvd_of_dvd_mul_left H)

theorem false_of_sl3_odd {n q : ℕ} (hn : 4 ≤ n) (hev : Even n) (hq : Odd q) (hq1 : 1 < q)
    (H : 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (q - 1) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : False := by
  have hcop : Nat.Coprime q (Nat.gcd 3 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (q - 1))
      ((Nat.coprime_self_sub_right hq1.le).mpr (Nat.coprime_one_right q))
  have hdvd : q ^ 3 ∣ (2 ^ n) ^ 2 - 1 := cube_dvd_of_odd hq hcop (H ▸ Dvd.intro _ rfl)
  have hle : q ^ 3 ≤ (2 ^ n) ^ 2 - 1 := Nat.le_of_dvd (pos_of_two_pow_sq_sub_one (by omega)) hdvd
  have hMlt := two_pow_sq_sub_one_lt n
  obtain ⟨m, hm⟩ := hev
  by_cases hn10 : n < 10
  · exact not_cube_dvd_small (by omega) (by omega) hdvd
  obtain ⟨s, rfl⟩ := hq
  have hs : s ≠ 0 := by omega
  have e2 : (2 * s + 1) ^ 2 - 1 = 4 * (s * (s + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 * s + 1) ^ 3 - 1 = 2 * (s * (4 * s ^ 2 + 6 * s + 3)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have hO : Odd ((2 * s + 1) ^ 3 * (4 * s ^ 2 + 6 * s + 3)) :=
    Nat.odd_mul.mpr ⟨(odd_two_mul_add_one s).pow, by
      rw [show 4 * s ^ 2 + 6 * s + 3 = 2 * (2 * s ^ 2 + 3 * s + 1) + 1 by ring]
      exact odd_two_mul_add_one _⟩
  have H' : 2 ^ n * (((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 * s + 1 - 1)) =
      2 ^ 3 * (s ^ 2 * ((s + 1) * ((2 * s + 1) ^ 3 * (4 * s ^ 2 + 6 * s + 3)))) := by
    rw [← mul_assoc, H, e2, e3]
    ring
  have hv := congrArg (padicValNat 2) H'
  rw [padicValNat_two_pow_mul_odd n (Nat.odd_mul.mpr ⟨odd_two_pow_sq_sub_one n
      (by omega), odd_gcd_three _⟩),
    padicValNat.mul (by positivity) (mul_ne_zero (pow_ne_zero 2 hs)
      (mul_ne_zero (Nat.add_one_ne_zero s) hO.pos.ne')), padicValNat.prime_pow,
    padicValNat.mul (pow_ne_zero 2 hs) (mul_ne_zero (Nat.add_one_ne_zero s) hO.pos.ne'),
    padicValNat.pow, padicValNat.mul (Nat.add_one_ne_zero s) hO.pos.ne',
    padicValNat.eq_zero_of_not_dvd hO.not_two_dvd_nat] at hv
  rcases Nat.even_or_odd s with ⟨r, hr⟩ | hso
  ·
    have h0 : padicValNat 2 (s + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    omega
  · have h0 : padicValNat 2 s = 0 := padicValNat.eq_zero_of_not_dvd hso.not_two_dvd_nat
    have hdv : 2 ^ (n - 3) ∣ s + 1 := by
      have h := pow_padicValNat_dvd (p := 2) (n := s + 1)
      rwa [show padicValNat 2 (s + 1) = n - 3 by omega] at h
    have hle' : 2 ^ (n - 3) ≤ s + 1 := Nat.le_of_dvd (by omega) hdv
    have h1 : (2 ^ (n - 3)) ^ 3 ≤ (2 * s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : 2 ^ (2 * n) ≤ (2 ^ (n - 3)) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem false_of_su3_odd {n q : ℕ} (hn : 4 ≤ n) (hev : Even n) (hq : Odd q) (hq1 : 1 < q)
    (H : 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (q + 1) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) : False := by
  have hcop : Nat.Coprime q (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (q + 1))
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right q))
  have hdvd : q ^ 3 ∣ (2 ^ n) ^ 2 - 1 := cube_dvd_of_odd hq hcop (H ▸ Dvd.intro _ rfl)
  have hle : q ^ 3 ≤ (2 ^ n) ^ 2 - 1 := Nat.le_of_dvd (pos_of_two_pow_sq_sub_one (by omega)) hdvd
  have hMlt := two_pow_sq_sub_one_lt n
  obtain ⟨m, hm⟩ := hev
  by_cases hn10 : n < 10
  · exact not_cube_dvd_small (by omega) (by omega) hdvd
  obtain ⟨s, rfl⟩ := hq
  have hs : s ≠ 0 := by omega
  have e2 : (2 * s + 1) ^ 2 - 1 = 4 * (s * (s + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have hO : Odd ((2 * s + 1) ^ 3 * (4 * s ^ 2 + 2 * s + 1)) :=
    Nat.odd_mul.mpr ⟨(odd_two_mul_add_one s).pow, by
      rw [show 4 * s ^ 2 + 2 * s + 1 = 2 * (2 * s ^ 2 + s) + 1 by ring]
      exact odd_two_mul_add_one _⟩
  have H' : 2 ^ n * (((2 ^ n) ^ 2 - 1) * Nat.gcd 3 (2 * s + 1 + 1)) =
      2 ^ 3 * (s * ((s + 1) ^ 2 * ((2 * s + 1) ^ 3 * (4 * s ^ 2 + 2 * s + 1)))) := by
    rw [← mul_assoc, H, e2]
    ring
  have hv := congrArg (padicValNat 2) H'
  rw [padicValNat_two_pow_mul_odd n (Nat.odd_mul.mpr ⟨odd_two_pow_sq_sub_one n
      (by omega), odd_gcd_three _⟩),
    padicValNat.mul (by positivity) (mul_ne_zero hs
      (mul_ne_zero (pow_ne_zero 2 (Nat.add_one_ne_zero s)) hO.pos.ne')), padicValNat.prime_pow,
    padicValNat.mul hs (mul_ne_zero (pow_ne_zero 2 (Nat.add_one_ne_zero s)) hO.pos.ne'),
    padicValNat.mul (pow_ne_zero 2 (Nat.add_one_ne_zero s)) hO.pos.ne', padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hO.not_two_dvd_nat] at hv
  rcases Nat.even_or_odd s with ⟨r, hr⟩ | hso
  · have h0 : padicValNat 2 (s + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    have hdv : 2 ^ (n - 3) ∣ s := by
      have h := pow_padicValNat_dvd (p := 2) (n := s)
      rwa [show padicValNat 2 s = n - 3 by omega] at h
    have hle' : 2 ^ (n - 3) ≤ s := Nat.le_of_dvd (by omega) hdv
    have h1 : (2 ^ (n - 3)) ^ 3 ≤ (2 * s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : 2 ^ (2 * n) ≤ (2 ^ (n - 3)) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    have h0 : padicValNat 2 s = 0 := padicValNat.eq_zero_of_not_dvd hso.not_two_dvd_nat
    omega

theorem isEmpty_mulEquiv_projSL_three_of_card_L2 {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n)
    (hev : Even n) (hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (K : Type) [Field K]
    [Finite K] : IsEmpty (X ≃* projSL 3 K) := by
  refine ⟨fun e => ?_⟩
  have hc := KFacts.KS14.card_projSL_three_mul_gcd K
  rw [← Nat.card_congr e.toEquiv, hX] at hc
  have := Fintype.ofFinite K
  obtain ⟨p, -, k, hp, hK⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hK] at hc
  by_cases hp2 : p = 2
  · subst hp2
    exact false_of_sl3_two (by omega) k.pos hc
  · exact false_of_sl3_odd hn hev (hp.odd_of_ne_two hp2).pow
      (Nat.one_lt_pow k.ne_zero hp.one_lt) hc

theorem isEmpty_mulEquiv_projSU_three_of_card_L2 {X : Type*} [Group X] {n : ℕ} (hn : 4 ≤ n)
    (hev : Even n) (hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (p f : ℕ) [Fact p.Prime]
    (hf : 1 ≤ f) : IsEmpty (X ≃* projSU 3 p f) := by
  refine ⟨fun e => ?_⟩
  have hp : p.Prime := Fact.out
  have hc := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  rw [← Nat.card_congr e.toEquiv, hX] at hc
  by_cases hp2 : p = 2
  · subst hp2
    exact false_of_su3_two (by omega) hf hc
  · exact false_of_su3_odd hn hev (hp.odd_of_ne_two hp2).pow
      (Nat.one_lt_pow (by omega) hp.one_lt) hc

theorem not_isLThreeEpsAt_of_card_L2 {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (p f : ℕ) [Fact p.Prime] :
    ¬ Sec14.IsLThreeEpsAt X p f := by
  rintro (⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three_of_card_L2 hn hev hX (GaloisField p f)).false φ
  · have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq
      · exact h
    exact (isEmpty_mulEquiv_projSU_three_of_card_L2 hn hev hX p f hf1).false φ

theorem not_isoLThreePi_of_card_L2 {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi X p e := by
  rintro (⟨-, ⟨φ⟩⟩ | ⟨he, ⟨φ⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three_of_card_L2 hn hev hX (GaloisField p e)).false φ
  · have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · simp at he
      · exact h
    exact (isEmpty_mulEquiv_projSU_three_of_card_L2 hn hev hX p e he1).false φ

theorem card_L2_ne {n : ℕ} (hn : 4 ≤ n) (hev : Even n) {N : ℕ} (hN : N ≤ 16776959)
    (h4 : N ≠ 4080) (h6 : N ≠ 262080) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ N := by
  obtain ⟨m, rfl⟩ := hev
  by_cases h8 : 8 ≤ m + m
  · have h1 : 256 ≤ 2 ^ (m + m) := by
      calc 256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (m + m) := Nat.pow_le_pow_right (by norm_num) h8
    have h2 : 256 ^ 2 ≤ (2 ^ (m + m)) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : 256 * 65535 ≤ 2 ^ (m + m) * ((2 ^ (m + m)) ^ 2 - 1) :=
      Nat.mul_le_mul h1 (by omega)
    omega
  · rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
    · norm_num
      omega
    · norm_num
      omega

end CFSG.RankThree.PartTwo.Sec15.Proof1523Res3
