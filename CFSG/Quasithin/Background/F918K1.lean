module

public import CFSG.Quasithin.Background.F918K0
public import CFSG.Quasithin.H13.VolIA38Orders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.H13.VolI

theorem NSCard.ge {N : ℕ} (h : NSCard N) : 660 ≤ N := by
  rcases h with rfl | ⟨p, hp, hp11, rfl⟩
  · norm_num
  · have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
    have h3 : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul hp11 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp11 2) 1)
    omega

theorem NSCard.exists_prime_dvd {N : ℕ} (h : NSCard N) : ∃ q : ℕ, q.Prime ∧ 11 ≤ q ∧ q ∣ N := by
  rcases h with rfl | ⟨p, hp, hp11, rfl⟩
  · exact ⟨11, by norm_num, le_rfl, by norm_num⟩
  · refine ⟨p, hp, hp11, ?_⟩
    have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
    have hd : p ∣ 2 * ordA 1 p := h2 ▸ dvd_mul_right p _
    exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) hd

theorem not_nsCard_of_dvd_smooth {N a b c d : ℕ} (h : N ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    ¬ NSCard N := by
  intro hN
  obtain ⟨q, hq, hq11, hqN⟩ := hN.exists_prime_dvd
  have hqd := hqN.trans h
  rcases hq.dvd_mul.1 hqd with h1 | h1
  · rcases hq.dvd_mul.1 h1 with h2 | h2
    · rcases hq.dvd_mul.1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h3)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h3)
        omega
    · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
      omega
  · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h1)
    omega

theorem not_nsCard_between {N p₀ : ℕ} (hJ : N ≠ 175560) (h1 : p₀ * (p₀ ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (p₀ + 1) * ((p₀ + 1) ^ 2 - 1)) : ¬ NSCard N := by
  rintro (h | ⟨p, hp, hp11, rfl⟩)
  · exact hJ h
  · have h3 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
    rcases le_or_gt p p₀ with hle | hlt
    · have h4 : p * (p ^ 2 - 1) ≤ p₀ * (p₀ ^ 2 - 1) :=
        Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
      omega
    · have h4 : (p₀ + 1) * ((p₀ + 1) ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
        Nat.mul_le_mul hlt (Nat.sub_le_sub_right (Nat.pow_le_pow_left hlt 2) 1)
      omega

theorem not_nsCard_95040 : ¬ NSCard 95040 :=
  not_nsCard_between (p₀ := 57) (by norm_num) (by norm_num) (by norm_num)

theorem not_nsCard_443520 : ¬ NSCard 443520 :=
  not_nsCard_between (p₀ := 96) (by norm_num) (by norm_num) (by norm_num)

theorem not_nsCard_10200960 : ¬ NSCard 10200960 :=
  not_nsCard_between (p₀ := 273) (by norm_num) (by norm_num) (by norm_num)

theorem not_nsCard_244823040 : ¬ NSCard 244823040 :=
  not_nsCard_between (p₀ := 788) (by norm_num) (by norm_num) (by norm_num)

theorem not_nsCard_9999360 : ¬ NSCard 9999360 :=
  not_nsCard_between (p₀ := 271) (by norm_num) (by norm_num) (by norm_num)

private theorem not_nsCard_of_two_pow {b M c k : ℕ} (hM : M = 2 ^ k) (hk : 4 ≤ k) (hdvd : M ∣ b)
    (hb : b ≤ M * ((M - 1) * c)) (hc : 2 * c + 2 < M) : ¬ NSCard b := by
  rintro (h | ⟨p, hp, hp11, h⟩)
  · have h16 : 2 ^ 4 ∣ b := (hM ▸ pow_dvd_pow 2 hk : 2 ^ 4 ∣ M).trans hdvd
    rw [h] at h16
    norm_num at h16
  · subst hM
    exact ordA_one_ne_of_two_pow hp (by omega) hdvd (two_mul_lt_of_le hb hc) h.symm

theorem not_nsCard_SL_three {n : ℕ} (hn : 2 ≤ n) :
    ¬ NSCard (2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1))) :=
  not_nsCard_of_two_pow (c := 2 ^ (2 * n)) (k := 3 * n) rfl (by omega) (dvd_mul_right _ _)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    (two_mul_pow_add_two_lt (by norm_num) (by omega) (by omega))

theorem not_nsCard_Sp4 {n : ℕ} (hn : 1 ≤ n) :
    ¬ NSCard (2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) := by
  refine not_nsCard_of_two_pow (c := 2 ^ (2 * n)) (k := 4 * n) rfl (by omega)
    (dvd_mul_right _ _) ?_ (two_mul_pow_add_two_lt (by norm_num) (by omega) (by omega))
  rw [mul_comm (2 ^ (2 * n) - 1)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

private theorem psu3_le {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ (q ^ 3 - 1) * q ^ 2 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : 2 * q ^ 2 ≤ q ^ 3 := by
    calc 2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
      _ = q ^ 3 := by ring
  zify [h1, h2] at h3 ⊢
  nlinarith

private theorem psu3_two_mul_lt {q : ℕ} (hq : 4 ≤ q) : 2 * q ^ 2 + 2 < q ^ 3 := by
  have h1 : 4 * q ^ 2 ≤ q ^ 3 := by
    calc 4 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
      _ = q ^ 3 := by ring
  have h2 : 16 ≤ q ^ 2 := by nlinarith
  omega

theorem not_nsCard_psu3 {a : ℕ} (ha : 2 ≤ a) :
    ¬ NSCard ((2 ^ a) ^ 3 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) / Nat.gcd 3 (2 ^ a + 1))) := by
  have hq4 : 4 ≤ 2 ^ a :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  refine not_nsCard_of_two_pow (c := (2 ^ a) ^ 2) (k := a * 3) (by rw [← pow_mul]) (by omega)
    (dvd_mul_right _ _) ?_ (psu3_two_mul_lt hq4)
  exact Nat.mul_le_mul_left _ ((Nat.div_le_self _ _).trans (psu3_le (by omega)))

theorem not_nsCard_psl3 {e : ℕ} (he : 2 ≤ e) : ¬ NSCard (ordA 2 (2 ^ e)) := by
  intro h
  have hA : A38Order (ordA 2 (2 ^ e)) := by
    rcases h with h | ⟨p, hp, hp11, h⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, by omega, h⟩))
  exact a38Order_not_rankTwoOrder hA (Or.inl ⟨e, he, rfl⟩)

end CFSG.Quasithin
