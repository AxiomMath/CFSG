module

public import CFSG.Quasithin.Vol2.Ch10SecKGC27b

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

@[expose] def FFOrd (N : ℕ) : Prop :=
  C27Order N ∨ (∃ m : ℕ, 1 ≤ m ∧ N = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) ∨
    (∃ m : ℕ, 1 ≤ m ∧ N = (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) ∨ N ∣ 12096

namespace FFOrd

theorem sixteen_dvd_sp4 {m : ℕ} (hm : 1 ≤ m) (x : ℕ) : 16 ∣ 2 ^ (4 * m) * x :=
  Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)) _

theorem sixteen_dvd_g2 {m : ℕ} (hm : 1 ≤ m) (x : ℕ) : 16 ∣ (2 ^ m) ^ 6 * x := by
  rw [← pow_mul]
  exact Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)) _

theorem prime_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ 24192) : p = 2 ∨ p = 3 ∨ p = 7 := by
  rw [show (24192 : ℕ) = 2 ^ 7 * 3 ^ 3 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))

theorem prime_of_dvd {p N : ℕ} (hp : p.Prime) (hN : N ∣ 12096) (hpN : p ∣ 2 * N) :
    p = 2 ∨ p = 3 ∨ p = 7 :=
  prime_dvd hp (hpN.trans (by simpa using Nat.mul_dvd_mul_left 2 hN))

theorem not_psl_p2_eq_sp4 {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : 1 ≤ m)
    (h : p ^ 2 * (p ^ 4 - 1) = 2 * (2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)))) :
    False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdvd := two_pow_dvd_sq_sub_one hodd (k := 4 * m)
    ⟨(2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1), by rw [h, pow_succ 2 (4 * m)]; ring⟩
  have e2 : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  have e4 : (2 : ℕ) ^ (4 * m) = (2 ^ m) ^ 4 := by rw [← pow_mul, mul_comm]
  rw [e2, e4] at h
  rw [e4] at hdvd
  have hq2 : 2 ≤ 2 ^ m := (show 2 = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hm
  set q := 2 ^ m with hq
  have h16 : 16 ≤ p ^ 2 := by nlinarith
  have hx : q ^ 4 + 1 ≤ p ^ 2 := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hR : 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ≤ q ^ 11 := by
    calc 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ≤ 2 * (q ^ 4 * (q ^ 2 * q ^ 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.sub_le _ _)))
      _ = 2 * q ^ 10 := by ring
      _ ≤ q * q ^ 10 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 11 := by ring
  have hL : q ^ 11 < p ^ 2 * (p ^ 4 - 1) := by
    have hp4 : q ^ 8 ≤ p ^ 4 - 1 := by
      have h1 : (q ^ 4 + 1) ^ 2 ≤ (p ^ 2) ^ 2 := Nat.pow_le_pow_left hx 2
      have h2 : (q ^ 4 + 1) ^ 2 = q ^ 8 + 2 * q ^ 4 + 1 := by ring
      have h3 : (p ^ 2) ^ 2 = p ^ 4 := by ring
      omega
    have h8 : 0 < q ^ 8 := by positivity
    have h12 : q ^ 11 ≤ q ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc q ^ 11 < (q ^ 4 + 1) * q ^ 8 := by
          rw [show (q ^ 4 + 1) * q ^ 8 = q ^ 12 + q ^ 8 by ring]
          omega
      _ ≤ p ^ 2 * (p ^ 4 - 1) := Nat.mul_le_mul hx hp4
  omega

theorem not_psl_p2_eq_g2 {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : 1 ≤ m)
    (h : p ^ 2 * (p ^ 4 - 1) = 2 * ((2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)))) :
    False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have e6 : (2 : ℕ) ^ (6 * m) = (2 ^ m) ^ 6 := by rw [← pow_mul, mul_comm]
  have hdvd := two_pow_dvd_sq_sub_one hodd (k := 6 * m)
    ⟨((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1), by rw [h, pow_succ 2 (6 * m), e6]; ring⟩
  rw [e6] at hdvd
  have hq2 : 2 ≤ 2 ^ m := (show 2 = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hm
  set q := 2 ^ m with hq
  have h16 : 16 ≤ p ^ 2 := by nlinarith
  have hx : q ^ 6 + 1 ≤ p ^ 2 := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hR : 2 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) ≤ q ^ 15 := by
    calc 2 * (q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1))) ≤ 2 * (q ^ 6 * (q ^ 6 * q ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.sub_le _ _)))
      _ = 2 * q ^ 14 := by ring
      _ ≤ q * q ^ 14 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 15 := by ring
  have hL : q ^ 15 < p ^ 2 * (p ^ 4 - 1) := by
    have hp4 : q ^ 12 ≤ p ^ 4 - 1 := by
      have h1 : (q ^ 6 + 1) ^ 2 ≤ (p ^ 2) ^ 2 := Nat.pow_le_pow_left hx 2
      have h2 : (q ^ 6 + 1) ^ 2 = q ^ 12 + 2 * q ^ 6 + 1 := by ring
      have h3 : (p ^ 2) ^ 2 = p ^ 4 := by ring
      omega
    have h12 : 0 < q ^ 12 := by positivity
    have h18 : q ^ 15 ≤ q ^ 18 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc q ^ 15 < (q ^ 6 + 1) * q ^ 12 := by
          rw [show (q ^ 6 + 1) * q ^ 12 = q ^ 18 + q ^ 12 by ring]
          omega
      _ ≤ p ^ 2 * (p ^ 4 - 1) := Nat.mul_le_mul hx hp4
  omega

end FFOrd

open FFOrd

theorem not_ffOrd_psl_p {p N : ℕ} (hp : p.Prime) (h5 : p ^ 2 % 5 = 1)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (hN : 2 * N = p * (p ^ 2 - 1)) : ¬ FFOrd N := by
  have h16 : ¬ 16 ∣ N := fun h => not_sixteen_dvd h8 (hN ▸ Dvd.dvd.mul_left h 2)
  rintro (h | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | h)
  · exact not_c27Order_psl_p hp h5 h8 hN h
  · exact h16 (sixteen_dvd_sp4 hm _)
  · exact h16 (sixteen_dvd_g2 hm _)
  · rcases prime_of_dvd hp h (hN ▸ Dvd.intro _ rfl) with rfl | rfl | rfl <;> omega

theorem not_ffOrd_psl_p2 {p N : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hN : 2 * N = p ^ 2 * (p ^ 4 - 1)) : ¬ FFOrd N := by
  rintro (h | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | h)
  · exact not_c27Order_psl_p2 hp hp3 hN h
  · exact not_psl_p2_eq_sp4 hp hp3 hm hN.symm
  · exact not_psl_p2_eq_g2 hp hp3 hm hN.symm
  · have hpN : p ∣ 2 * N := hN ▸ Dvd.dvd.mul_right (dvd_pow_self p (by norm_num)) _
    rcases prime_of_dvd hp h hpN with rfl | rfl | rfl
    · omega
    · omega
    · have := Nat.le_of_dvd (by norm_num) (Nat.mul_dvd_mul_left 2 h)
      norm_num at hN
      omega

theorem not_ffOrd_j1 : ¬ FFOrd 175560 := by
  have h16 : ¬ (16 : ℕ) ∣ 175560 := by norm_num
  rintro (h | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | h)
  · exact not_c27Order_j1 h
  · exact h16 (h ▸ sixteen_dvd_sp4 hm _)
  · exact h16 (h ▸ sixteen_dvd_g2 hm _)
  · norm_num at h

theorem q_facts {Q : Type} [Group Q]
    (hQ : (∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 Q ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 Q) ∨ IsSporadic .J1 Q) :
    IsSimpleGroup Q ∧ ¬ FFOrd (Nat.card Q) ∧ 6 < Nat.card Q := by
  refine ⟨(SecB.C10KG.q_facts hQ).1, ?_⟩
  rcases hQ with ⟨p, hp, hpsl, h5, h8⟩ | ⟨p, hp, hp3, hpsl⟩ | ⟨⟨e⟩⟩
  · have hN : 2 * Nat.card Q = p * (p ^ 2 - 1) := by
      have := two_mul_card_psl2 hpsl (by omega)
      simpa using this
    refine ⟨not_ffOrd_psl_p hp h5 h8 hN, ?_⟩
    have hp11 : 11 ≤ p := by
      by_contra hlt
      have : p = 3 ∨ p = 5 := by omega
      rcases this with rfl | rfl <;> norm_num at h5
    have h121 : 11 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp11 2
    have : 11 * 120 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp11 (by omega)
    omega
  · have hN : 2 * Nat.card Q = p ^ 2 * (p ^ 4 - 1) := by
      rw [two_mul_card_psl2 hpsl (by omega), ← pow_mul]
    refine ⟨not_ffOrd_psl_p2 hp hp3 hN, ?_⟩
    have h16 : 4 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h256 : 4 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have : 16 * 255 ≤ p ^ 2 * (p ^ 4 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F134.card_carrier_J1]
    exact ⟨not_ffOrd_j1, by norm_num⟩

end CFSG.Quasithin.Vol2.Ch10.V1C
