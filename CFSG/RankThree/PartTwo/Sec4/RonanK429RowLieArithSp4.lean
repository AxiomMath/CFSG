module

public import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

private theorem sp4Arith_two_pow_lt {a b u v : ℕ} (hab : a < b) (hu : Odd u)
    (h : 2 ^ a * u = 2 ^ b * v) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have hk : 1 ≤ k := by omega
  rw [pow_add, mul_assoc] at h
  have h' : u = 2 ^ k * v := Nat.eq_of_mul_eq_mul_left (by positivity) h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h2 : u = 2 * (2 ^ j * v) := by rw [h']; ring
  have hu2 := Nat.odd_iff.mp hu
  omega

private theorem sp4Arith_two_pow_inj {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (sp4Arith_two_pow_lt hab hu h).elim
  · exact hab
  · exact (sp4Arith_two_pow_lt hab hv h.symm).elim

private theorem sp4Arith_odd_sub_one {k j : ℕ} (hk : 1 ≤ k) (hj : j ≠ 0) :
    Odd ((2 ^ k) ^ j - 1) := by
  have hk2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h2 : 2 ∣ (2 ^ k) ^ j := dvd_pow hk2 hj
  have hpos : 0 < (2 ^ k) ^ j := by positivity
  exact Nat.odd_iff.mpr (by omega)

private theorem sp4Arith_odd_add_one {k j : ℕ} (hk : 1 ≤ k) (hj : j ≠ 0) :
    Odd ((2 ^ k) ^ j + 1) := by
  have hk2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h2 : 2 ∣ (2 ^ k) ^ j := dvd_pow hk2 hj
  exact Nat.odd_iff.mpr (by omega)

private theorem sp4Arith_eight_gt {x : ℕ} (hx : 2 ≤ x) : 3 * (x ^ 6 - 1) < x ^ 8 - 1 := by
  have h4 : 4 ≤ x ^ 2 := by nlinarith
  have h8 : 4 * x ^ 6 ≤ x ^ 8 := by
    have e : x ^ 8 = x ^ 2 * x ^ 6 := by ring
    rw [e]
    exact Nat.mul_le_mul h4 (le_refl _)
  have h6 : 0 < x ^ 6 := pow_pos (by omega) 6
  omega

private theorem sp4Arith_L3_contra {x : ℕ} (hx : 2 ≤ x)
    (h : (x ^ 3) ^ 4 * (((x ^ 3) ^ 2 - 1) * ((x ^ 3) ^ 4 - 1)) * 3 =
      (x ^ 4) ^ 3 * (((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 3 - 1))) : False := by
  rw [show (x ^ 3) ^ 4 = x ^ 12 by ring, show (x ^ 3) ^ 2 = x ^ 6 by ring,
    show (x ^ 4) ^ 3 = x ^ 12 by ring, show (x ^ 4) ^ 2 = x ^ 8 by ring] at h
  have hA := sp4Arith_eight_gt hx
  have h12 : 2 ≤ x ^ 12 := le_trans hx (Nat.le_self_pow (by norm_num) x)
  have hP : 0 < x ^ 12 := by omega
  have hB : 0 < x ^ 12 - 1 := by omega
  have h1 : (x ^ 6 - 1) * (x ^ 12 - 1) * 3 < (x ^ 8 - 1) * (x ^ 12 - 1) := by
    calc (x ^ 6 - 1) * (x ^ 12 - 1) * 3 = (3 * (x ^ 6 - 1)) * (x ^ 12 - 1) := by ring
      _ < (x ^ 8 - 1) * (x ^ 12 - 1) := Nat.mul_lt_mul_of_pos_right hA hB
  have h2 : x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1) * 3) <
      x ^ 12 * ((x ^ 8 - 1) * (x ^ 12 - 1)) := Nat.mul_lt_mul_of_pos_left h1 hP
  have h3 : x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1)) * 3 =
      x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1) * 3) := by ring
  omega

private theorem sp4Arith_U3_contra {x : ℕ} (hx : 2 ≤ x)
    (h : (x ^ 3) ^ 4 * (((x ^ 3) ^ 2 - 1) * ((x ^ 3) ^ 4 - 1)) * 3 =
      (x ^ 4) ^ 3 * (((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 3 + 1))) : False := by
  rw [show (x ^ 3) ^ 4 = x ^ 12 by ring, show (x ^ 3) ^ 2 = x ^ 6 by ring,
    show (x ^ 4) ^ 3 = x ^ 12 by ring, show (x ^ 4) ^ 2 = x ^ 8 by ring] at h
  have hA := sp4Arith_eight_gt hx
  have h12 : 2 ≤ x ^ 12 := le_trans hx (Nat.le_self_pow (by norm_num) x)
  have hP : 0 < x ^ 12 := by omega
  have hD : x ^ 12 - 1 ≤ x ^ 12 + 1 := by omega
  have h1 : (x ^ 6 - 1) * (x ^ 12 - 1) * 3 < (x ^ 8 - 1) * (x ^ 12 + 1) := by
    calc (x ^ 6 - 1) * (x ^ 12 - 1) * 3 ≤ (x ^ 6 - 1) * (x ^ 12 + 1) * 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hD) (le_refl _)
      _ = (3 * (x ^ 6 - 1)) * (x ^ 12 + 1) := by ring
      _ < (x ^ 8 - 1) * (x ^ 12 + 1) := Nat.mul_lt_mul_of_pos_right hA (by omega)
  have h2 : x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1) * 3) <
      x ^ 12 * ((x ^ 8 - 1) * (x ^ 12 + 1)) := Nat.mul_lt_mul_of_pos_left h1 hP
  have h3 : x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1)) * 3 =
      x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1) * 3) := by ring
  omega

private theorem sp4Arith_two_L3 {m e : ℕ} (hm : 2 ≤ m) (he : 1 ≤ e)
    (hEq : (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 =
      (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1))) : False := by
  have hU : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3) :=
    Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨sp4Arith_odd_sub_one (by omega) (by norm_num),
      sp4Arith_odd_sub_one (by omega) (by norm_num)⟩, Nat.odd_iff.mpr rfl⟩
  have hV : Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) :=
    Nat.odd_mul.mpr ⟨sp4Arith_odd_sub_one (by omega) (by norm_num),
      sp4Arith_odd_sub_one (by omega) (by norm_num)⟩
  have e1 : (2 : ℕ) ^ (m * 4) = (2 ^ m) ^ 4 := pow_mul 2 m 4
  have e2 : (2 : ℕ) ^ (e * 3) = (2 ^ e) ^ 3 := pow_mul 2 e 3
  have key : (2 : ℕ) ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3) =
      (2 : ℕ) ^ (e * 3) * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) := by
    rw [e1, e2]
    calc (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3)
        = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 := by ring
      _ = (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) := hEq
  have hme : m * 4 = e * 3 := sp4Arith_two_pow_inj hU hV key
  obtain ⟨c, rfl⟩ : ∃ c, m = 3 * c := ⟨m / 3, by omega⟩
  obtain rfl : e = 4 * c := by omega
  have hc : 1 ≤ c := by omega
  have hx : 2 ≤ 2 ^ c := Nat.le_self_pow (by omega) 2
  have e3 : (2 : ℕ) ^ (3 * c) = (2 ^ c) ^ 3 := by rw [← pow_mul, mul_comm]
  have e4 : (2 : ℕ) ^ (4 * c) = (2 ^ c) ^ 4 := by rw [← pow_mul, mul_comm]
  rw [e3, e4] at hEq
  exact sp4Arith_L3_contra hx hEq

private theorem sp4Arith_two_U3 {m e : ℕ} (hm : 2 ≤ m) (he : 1 ≤ e)
    (hEq : (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 =
      (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1))) : False := by
  have hU : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3) :=
    Nat.odd_mul.mpr ⟨Nat.odd_mul.mpr ⟨sp4Arith_odd_sub_one (by omega) (by norm_num),
      sp4Arith_odd_sub_one (by omega) (by norm_num)⟩, Nat.odd_iff.mpr rfl⟩
  have hV : Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) :=
    Nat.odd_mul.mpr ⟨sp4Arith_odd_sub_one (by omega) (by norm_num),
      sp4Arith_odd_add_one (by omega) (by norm_num)⟩
  have e1 : (2 : ℕ) ^ (m * 4) = (2 ^ m) ^ 4 := pow_mul 2 m 4
  have e2 : (2 : ℕ) ^ (e * 3) = (2 ^ e) ^ 3 := pow_mul 2 e 3
  have key : (2 : ℕ) ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3) =
      (2 : ℕ) ^ (e * 3) * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := by
    rw [e1, e2]
    calc (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) * 3)
        = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 := by ring
      _ = (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) := hEq
  have hme : m * 4 = e * 3 := sp4Arith_two_pow_inj hU hV key
  obtain ⟨c, rfl⟩ : ∃ c, m = 3 * c := ⟨m / 3, by omega⟩
  obtain rfl : e = 4 * c := by omega
  have hc : 1 ≤ c := by omega
  have hx : 2 ≤ 2 ^ c := Nat.le_self_pow (by omega) 2
  have e3 : (2 : ℕ) ^ (3 * c) = (2 ^ c) ^ 3 := by rw [← pow_mul, mul_comm]
  have e4 : (2 : ℕ) ^ (4 * c) = (2 ^ c) ^ 4 := by rw [← pow_mul, mul_comm]
  rw [e3, e4] at hEq
  exact sp4Arith_U3_contra hx hEq

private theorem sp4Arith_odd_prime_pow {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (hp3 : p ≠ 3)
    (he : 1 ≤ e) : Odd (p ^ e) ∧ 5 ≤ p ^ e ∧ ¬ 3 ∣ p ^ e := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h2' := Nat.odd_iff.mp hodd
    omega
  have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  refine ⟨hodd.pow, by omega, ?_⟩
  intro h3
  have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  have h3eq : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
  omega

theorem sp4_mul_three_ne_L3 {m p e : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 ≠
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
  intro hEq
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact sp4Arith_two_L3 hm he hEq
  · obtain ⟨hQodd, hQ5, hQ3⟩ := sp4Arith_odd_prime_pow hp hodd hp3 he
    have key : (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) =
        3 * (2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by
      rw [pow_mul]
      calc (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)
          = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by ring
        _ = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 := hEq.symm
        _ = 3 * ((2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by ring
    exact CFSG.RankThree.PartTwo.Sec19.Step1917Steps.false_of_sl3Order_eq_sp4
      hQodd hQ5 hQ3 (by omega) (Or.inl key)

theorem sp4_mul_three_ne_U3 {m p e : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) :
    (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 ≠
      (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
  intro hEq
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact sp4Arith_two_U3 hm he hEq
  · obtain ⟨hQodd, hQ5, hQ3⟩ := sp4Arith_odd_prime_pow hp hodd hp3 he
    have key : (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) =
        3 * (2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by
      rw [pow_mul]
      calc (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)
          = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by ring
        _ = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) * 3 := hEq.symm
        _ = 3 * ((2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) := by ring
    exact CFSG.RankThree.PartTwo.Sec19.Step1917Steps.false_of_sl3Order_eq_sp4
      hQodd hQ5 hQ3 (by omega) (Or.inr key)

theorem sp4two_L3 {N r : ℕ} (hN : N ∣ 720) (hr2 : 2 ≤ r) (hr3 : r % 3 = 1)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) : False := by
  have hN' : N ≤ 720 := Nat.le_of_dvd (by norm_num) hN
  have hr4 : 4 ≤ r := by omega
  have h1 : 64 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr4 3)
  have h2 : 15 ≤ r ^ 2 - 1 := by
    have : 16 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr4 2)
    omega
  have h3 : 63 ≤ r ^ 3 - 1 := by omega
  have h4 : 64 * (15 * 63) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  omega

theorem sp4two_U3 {N r : ℕ} (hN : N ∣ 720) (hr2 : 2 ≤ r) (hr3 : r % 3 = 2)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1))) : r = 2 := by
  have hN' : N ≤ 720 := Nat.le_of_dvd (by norm_num) hN
  by_contra hne
  have hr5 : 5 ≤ r := by omega
  have h1 : 125 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr5 3)
  have h2 : 24 ≤ r ^ 2 - 1 := by
    have : 25 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr5 2)
    omega
  have h3 : 126 ≤ r ^ 3 + 1 := by omega
  have h4 : 125 * (24 * 126) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  omega

theorem f4two_L3 {N r : ℕ} (hN : N ∣ 35942400) (hr2 : 2 ≤ r) (hr3 : r % 3 = 1)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) : False := by
  have hN' : N ≤ 35942400 := Nat.le_of_dvd (by norm_num) hN
  have hr10 : r ≤ 10 := by
    by_contra hbig
    have hr11 : 11 ≤ r := by omega
    have h1 : 1331 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr11 3)
    have h2 : 120 ≤ r ^ 2 - 1 := by
      have : 121 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr11 2)
      omega
    have h3 : 1330 ≤ r ^ 3 - 1 := by omega
    have h4 : 1331 * (120 * 1330) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega
  have hN3 : N = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) / 3 := by omega
  subst hN3
  interval_cases r
  all_goals (try omega)
  all_goals (norm_num at hN)

theorem f4two_U3 {N r : ℕ} (hN : N ∣ 35942400) (hr2 : 2 ≤ r) (hr3 : r % 3 = 2)
    (h : N * 3 = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1))) : r = 2 := by
  have hN' : N ≤ 35942400 := Nat.le_of_dvd (by norm_num) hN
  have hr8 : r ≤ 8 := by
    by_contra hbig
    have hr11 : 11 ≤ r := by omega
    have h1 : 1331 ≤ r ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hr11 3)
    have h2 : 120 ≤ r ^ 2 - 1 := by
      have : 121 ≤ r ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hr11 2)
      omega
    have h3 : 1332 ≤ r ^ 3 + 1 := by omega
    have h4 : 1331 * (120 * 1332) ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega
  have hN3 : N = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) / 3 := by omega
  subst hN3
  interval_cases r
  all_goals (try omega)
  all_goals (norm_num at hN)

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
