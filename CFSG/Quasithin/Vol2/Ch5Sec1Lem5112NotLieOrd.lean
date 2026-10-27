module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112EvenOrd

public section

namespace CFSG.Quasithin.H13.EvenOrd

open CFSG.Open

theorem excl_one : Excl 1 :=
  Excl.of_profile (a := 0) (r := 1) odd_one (by norm_num)
    (fun n f hn hf _ hN => absurd hN (Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos (by omega) (Nat.div_pos (by nlinarith) (by norm_num)))))
    (fun n f hn hf _ hN => absurd hN (Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos (by omega) (Nat.div_pos (by nlinarith) (by norm_num)))))
    (fun n f hn hf _ hN => absurd hN (Nat.pos_iff_ne_zero.mp
      (Nat.mul_pos (by omega) (by nlinarith))))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_2520 : Excl 2520 :=
  Excl.of_profile (a := 3) (r := 315) ⟨157, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_7800 : Excl 7800 :=
  Excl.of_profile (a := 3) (r := 975) ⟨487, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_372000 : Excl 372000 :=
  Excl.of_profile (a := 5) (r := 11625) ⟨5812, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_126000 : Excl 126000 :=
  Excl.of_profile (a := 4) (r := 7875) ⟨3937, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_443520 : Excl 443520 :=
  Excl.of_profile (a := 7) (r := 3465) ⟨1732, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_10200960 : Excl 10200960 :=
  Excl.of_profile (a := 7) (r := 79695) ⟨39847, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_175560 : Excl 175560 :=
  Excl.of_profile (a := 3) (r := 21945) ⟨10972, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_604800 : Excl 604800 :=
  Excl.of_profile (a := 7) (r := 4725) ⟨2362, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_J4 : Excl 86775571046077562880 :=
  Excl.of_profile (a := 21) (r := 41377816699065) ⟨20688908349532, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_odd (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_44352000 : Excl 44352000 :=
  Excl.of_profile (a := 9) (r := 86625) ⟨43312, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (omega_of_lt (by norm_num)) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ _ h => by omega) (fun _ _ _ h => by omega) (by decide)

theorem excl_Ru : Excl 145926144000 :=
  Excl.of_profile (a := 14) (r := 8906625) ⟨4453312, by norm_num⟩ (by norm_num)
    (psl_of_bounded (by decide)) (psu_of_bounded (by decide)) (psp_of_bounded (by decide))
    (fun n f hn hf hN => by
      exfalso
      have : 12 ≤ n * (n - 1) := by
        have : 3 ≤ n - 1 := by omega
        nlinarith
      have h2 : n * (n - 1) ≤ 14 := by
        rw [← hN]
        exact Nat.le_mul_of_pos_left _ hf
      have h3 : n ≤ 4 := by
        by_contra h5
        have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hn4 : n = 4 := by omega
      subst hn4
      omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega)
    (fun f _ _ h => by
      obtain rfl : f = 7 := by omega
      decide)
    (fun _ _ _ h => by omega) (by decide)

theorem eleven_le_of_cong {p : ℕ} (hp : p.Prime) (h5 : p ^ 2 % 5 = 1)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> simp_all (config := { decide := true })

theorem psl2_two_part {p : ℕ} (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    ∃ r, Odd r ∧ p * (p ^ 2 - 1) / 2 = 2 ^ 2 * r := by
  rcases h8 with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, p = 8 * j + 3 := ⟨p / 8, by omega⟩
    refine ⟨(8 * j + 3) * (8 * j ^ 2 + 6 * j + 1), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 1, by ring⟩ ⟨4 * j ^ 2 + 3 * j, by ring⟩
    · have e : (8 * j + 3) ^ 2 - 1 = 8 * (8 * j ^ 2 + 6 * j + 1) := by
        have : (8 * j + 3) ^ 2 = 8 * (8 * j ^ 2 + 6 * j + 1) + 1 := by ring
        omega
      rw [e, show (8 * j + 3) * (8 * (8 * j ^ 2 + 6 * j + 1)) =
        2 * (2 ^ 2 * ((8 * j + 3) * (8 * j ^ 2 + 6 * j + 1))) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, p = 8 * j + 5 := ⟨p / 8, by omega⟩
    refine ⟨(8 * j + 5) * (8 * j ^ 2 + 10 * j + 3), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 2, by ring⟩ ⟨4 * j ^ 2 + 5 * j + 1, by ring⟩
    · have e : (8 * j + 5) ^ 2 - 1 = 8 * (8 * j ^ 2 + 10 * j + 3) := by
        have : (8 * j + 5) ^ 2 = 8 * (8 * j ^ 2 + 10 * j + 3) + 1 := by ring
        omega
      rw [e, show (8 * j + 5) * (8 * (8 * j ^ 2 + 10 * j + 3)) =
        2 * (2 ^ 2 * ((8 * j + 5) * (8 * j ^ 2 + 10 * j + 3))) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)

theorem excl_psl2 {p : ℕ} (hp11 : 11 ≤ p) (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    Excl (p * (p ^ 2 - 1) / 2) := by
  obtain ⟨r, hr, hm⟩ := psl2_two_part h8
  have hbig : 660 ≤ p * (p ^ 2 - 1) / 2 := by
    have h1 : 120 ≤ p ^ 2 - 1 := by
      have : 121 ≤ p ^ 2 := by nlinarith
      omega
    have h2 : 1320 ≤ p * (p ^ 2 - 1) := by nlinarith
    omega
  refine Excl.of_profile hr hm (fun n f hn hf hne hN => ?_) (fun n f hn hf _ hN => ?_)
    (fun n f hn hf _ hN => ?_) (omega_of_lt (by norm_num)) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ h => by omega)
    (fun _ _ h => by omega) (fun _ _ h => by omega) (fun _ _ _ h => by omega)
    (fun _ _ _ h => by omega) ?_
  ·
    have hn1 : n = 1 := by
      by_contra hne1
      have h3 : 3 ≤ n * (n + 1) / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num)).2
          (by simpa using Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 3 ≤ n + 1))
      have : n * (n + 1) / 2 ≤ f * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hf
      omega
    subst hn1
    obtain rfl : f = 2 := by simpa using hN
    rw [show ordA 1 (2 ^ 2) = 60 by decide]
    omega
  · exfalso
    have h3 : 3 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2
      (by simpa using Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 3 ≤ n + 1))
    have : n * (n + 1) / 2 ≤ f * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  · exfalso
    have : 4 ≤ n * n := by nlinarith
    have : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ hf
    omega
  · rw [hm]
    intro h
    obtain ⟨s, rfl⟩ := hr
    have h1 := congrArg (· % 8) h
    norm_num [ordTits] at h1
    omega

end CFSG.Quasithin.H13.EvenOrd
