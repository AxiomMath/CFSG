module

public import CFSG.Quasithin.Vol2.Ch1EightFourNum

public section

namespace CFSG.Quasithin.Ch1Four

theorem fin_L {f d m : ℕ} (hf : 2 ≤ f) (hd : d = 1 ∨ (d = 3 ∧ 3 ≤ f ∧ 3 ∣ 2 ^ f - 1))
    (hm : m * d = (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  have hd3 : d ≤ 3 := by rcases hd with rfl | ⟨rfl, -⟩ <;> norm_num
  rcases Nat.lt_or_ge f 4 with hf4 | hf4
  · interval_cases f
    · rcases hd with rfl | ⟨-, h3, -⟩
      · norm_num at hm
        exact not_fin_of_odd (a := 6) (o := 945) (by rw [hm]; norm_num) (by decide) (by decide)
          c hc k hk
      · omega
    · rcases hd with rfl | ⟨-, -, h3⟩
      · norm_num at hm
        exact not_fin_of_odd (a := 9) (o := 32193) (by rw [hm]; norm_num) (by decide)
          (by decide) c hc k hk
      · norm_num at h3
  · have hq : 16 ≤ 2 ^ f := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    generalize 2 ^ f = q at hq hm
    have h1 : 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 3) (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    have h2 : m * d ≤ m * 3 := Nat.mul_le_mul_left _ hd3
    omega

theorem fin_U {f d m : ℕ} (hf : 2 ≤ f) (hd : d = 1 ∨ (d = 3 ∧ 3 ∣ 2 ^ f + 1))
    (hm : m * d = (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  have hd3 : d ≤ 3 := by rcases hd with rfl | ⟨rfl, -⟩ <;> norm_num
  rcases Nat.lt_or_ge f 4 with hf4 | hf4
  · interval_cases f
    · rcases hd with rfl | ⟨-, h3⟩
      · norm_num at hm
        exact not_fin_of_odd (a := 6) (o := 975) (by rw [hm]; norm_num) (by decide) (by decide)
          c hc k hk
      · norm_num at h3
    · rcases hd with rfl | ⟨rfl, -⟩
      · norm_num at hm
        exact not_fin_of_odd (a := 9) (o := 32319) (by rw [hm]; norm_num) (by decide)
          (by decide) c hc k hk
      · norm_num at hm
        have hm' : m = 5515776 := by omega
        exact not_fin_of_odd (a := 9) (o := 10773) (by rw [hm']; norm_num) (by decide)
          (by decide) c hc k hk
  · have hq : 16 ≤ 2 ^ f := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    generalize 2 ^ f = q at hq hm
    have h1 : 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 + 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 3) (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.add_le_add_right (Nat.pow_le_pow_left hq 3) 1))
    have h2 : m * d ≤ m * 3 := Nat.mul_le_mul_left _ hd3
    omega

theorem fin_Sp {f m : ℕ} (hf : 2 ≤ f)
    (hm : m = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  rcases Nat.lt_or_ge f 3 with hf3 | hf3
  · interval_cases f
    norm_num at hm
    exact not_fin_of_odd (a := 8) (o := 3825) (by rw [hm]; norm_num) (by decide) (by decide)
      c hc k hk
  · have hq : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    generalize 2 ^ f = q at hq hm
    have h1 : 8 ^ 4 * ((8 ^ 2 - 1) * (8 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 4) (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    omega

theorem fin_G2 {f m : ℕ} (hf : 2 ≤ f)
    (hm : m = (2 ^ f) ^ 6 * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  generalize 2 ^ f = q at hq hm
  have h1 : 4 ^ 6 * ((4 ^ 6 - 1) * (4 ^ 2 - 1)) ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hq 6) (Nat.mul_le_mul
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
  omega

theorem fin_D4 {f m : ℕ} (hf : 1 ≤ f)
    (hm : m = (2 ^ f) ^ 12 * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 2 - 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  · interval_cases f
    norm_num at hm
    exact not_fin_of_odd (a := 12) (o := 51597) (by rw [hm]; norm_num) (by decide) (by decide)
      c hc k hk
  · have hq : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    generalize 2 ^ f = q at hq hm
    have h1 : 4 ^ 20 ≤ q ^ 20 := Nat.pow_le_pow_left hq 20
    have h2 : q ^ 20 ≤ m := by
      rw [hm, show q ^ 20 = q ^ 12 * q ^ 8 by ring]
      refine Nat.mul_le_mul_left _ ?_
      have h6 : 4 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
      have h2' : 4 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      calc q ^ 8 ≤ q ^ 8 + q ^ 4 + 1 := by omega
        _ = (q ^ 8 + q ^ 4 + 1) * 1 * 1 := by ring
        _ ≤ (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega

theorem fin_F4 {f m : ℕ} (hf : 3 ≤ f)
    (hm : m = (2 ^ f) ^ 12 * (((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
      (2 ^ f - 1))) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k hk
  have hle := le_of_fin hc hk
  have hq : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  generalize 2 ^ f = q at hq hm
  have h1 : 8 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have h2 : q ^ 12 ≤ m := by
    rw [hm]
    refine Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) ?_)
      (by positivity)) (by omega))
    have : 8 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  omega

theorem c2Shape_L {f d m : ℕ} (hf : 2 ≤ f) (hd : d = 1 ∨ (d = 3 ∧ 3 ≤ f ∧ 3 ∣ 2 ^ f - 1))
    (hm : m * d = (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))) : C2Shape m := by
  have hfin := fin_L hf hd hm
  replace hd : d = 1 ∨ (d = 3 ∧ 3 ∣ 2 ^ f - 1) := hd.imp id (fun h => ⟨h.1, h.2.2⟩)
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm hd h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hB := (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 2)).mul
    (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 3))
  refine ⟨hfin, ?_, f, 3, d, ((q ^ 2 - 1) * (q ^ 3 - 1)), q ^ 2 + q + 1, by omega, by norm_num,
    hd.imp id (fun h => h.1), ?_, hB, ?_, ?_, ?_⟩
  ·
    rcases hd with rfl | ⟨rfl, h3⟩
    · rw [mul_one] at hm
      rw [hm]
      exact Dvd.dvd.mul_left (h2f.mul_right _) _
    · have h9 : 3 * 3 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
        refine Nat.mul_dvd_mul h2f ?_
        rw [cube_sub_one_eq hq1]
        exact h3.mul_right _
      have : 3 * 3 ∣ m * 3 := hm ▸ h9.mul_left _
      rw [mul_comm m 3] at this
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  · rw [pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h1 : (q ^ 2 - 1) * (q ^ 3 - 1) ≤ q ^ 2 * q ^ 3 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h2 : q ^ 2 * q ^ 3 = q ^ 5 := by ring
    have h3 := pow_add_one_lt_pow (q := q) (a := 5) (b := 2 * 3) (by omega) (by norm_num)
      (by norm_num)
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rw [sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
    · rw [cube_sub_one_eq hq1] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · exact Nat.le_of_dvd (by positivity) h'
  · rw [pow_mul, ← hq]
    nlinarith

theorem c2Shape_U {f d m : ℕ} (hf : 2 ≤ f) (hd : d = 1 ∨ (d = 3 ∧ 3 ∣ 2 ^ f + 1))
    (hm : m * d = (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))) : C2Shape m := by
  have hfin := fin_U hf hd hm
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm hd h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hB := (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 2)).mul
    (odd_pow_add_one_of_even hev (by norm_num : 1 ≤ 3))
  refine ⟨hfin, ?_, f, 3, d, ((q ^ 2 - 1) * (q ^ 3 + 1)), q ^ 2 + q + 1, by omega, by norm_num,
    hd.imp id (fun h => h.1), ?_, hB, ?_, ?_, ?_⟩
  · rcases hd with rfl | ⟨rfl, h3⟩
    · rw [mul_one] at hm
      rw [hm]
      exact Dvd.dvd.mul_left (h2f.mul_right _) _
    · have h9 : 3 * 3 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
        refine Nat.mul_dvd_mul h2f ?_
        rw [cube_add_one_eq hq1]
        exact h3.mul_right _
      have : 3 * 3 ∣ m * 3 := hm ▸ h9.mul_left _
      rw [mul_comm m 3] at this
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  · rw [pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 2 * (2 * q ^ 3) :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by have := Nat.one_le_pow 3 q (by omega); omega)
    have h2 : q ^ 6 = q * q ^ 5 := by ring
    have h3 : q ^ 2 * (2 * q ^ 3) = 2 * q ^ 5 := by ring
    have h4 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
    have h5 : 4 * q ^ 5 ≤ q * q ^ 5 := Nat.mul_le_mul_right _ hq4
    show (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ (2 * 3) - 1
    rw [show 2 * 3 = 6 by norm_num]
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rw [sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
    · rw [cube_add_one_eq hq1] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
  · rw [pow_mul, ← hq]
    nlinarith

theorem c2Shape_Sp {f m : ℕ} (hf : 2 ≤ f)
    (hm : m = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1))) : C2Shape m := by
  have hfin := fin_Sp hf hm
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hB := (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 2)).mul
    (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 4))
  refine ⟨hfin, ?_, f, 4, 1, ((q ^ 2 - 1) * (q ^ 4 - 1)), q ^ 2 + 1, by omega, by norm_num,
    Or.inl rfl, ?_, hB, ?_, ?_, ?_⟩
  · rw [hm]
    exact Dvd.dvd.mul_left (h2f.mul_right _) _
  · rw [mul_one, pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h1 : (q ^ 2 - 1) * (q ^ 4 - 1) ≤ q ^ 2 * q ^ 4 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h2 : q ^ 2 * q ^ 4 = q ^ 6 := by ring
    have h3 := pow_add_one_lt_pow (q := q) (a := 6) (b := 2 * 4) (by omega) (by norm_num)
      (by norm_num)
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rw [sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
    · rw [four_sub_one_eq hq1, sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
        · have := Nat.le_of_dvd (by omega) h''
          omega
        · have := Nat.le_of_dvd (by omega) h''
          omega
      · exact Nat.le_of_dvd (by positivity) h'
  · rw [pow_mul, ← hq]
    nlinarith

theorem c2Shape_G2 {f m : ℕ} (hf : 2 ≤ f)
    (hm : m = (2 ^ f) ^ 6 * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) : C2Shape m := by
  have hfin := fin_G2 hf hm
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB := (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 6)).mul
    (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 2))
  refine ⟨hfin, ?_, f, 6, 1, ((q ^ 6 - 1) * (q ^ 2 - 1)), q ^ 3 + 1, by omega, by norm_num,
    Or.inl rfl, ?_, hB, ?_, ?_, ?_⟩
  · rw [hm]
    exact Dvd.dvd.mul_left (h2f.mul_left _) _
  · rw [mul_one, pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h1 : (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have h2 : q ^ 6 * q ^ 2 = q ^ 8 := by ring
    have h3 := pow_add_one_lt_pow (q := q) (a := 8) (b := 2 * 6) (by omega) (by norm_num)
      (by norm_num)
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rw [six_sub_one_eq hq1] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by have := Nat.one_le_pow 3 q (by omega); omega) h'
        omega
      · exact Nat.le_of_dvd (by positivity) h'
    · rw [sq_sub_one_eq] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'
        omega
      · have := Nat.le_of_dvd (by omega) h'
        omega
  · rw [pow_mul, ← hq]
    nlinarith

theorem c2Shape_D4 {f m : ℕ} (hf : 1 ≤ f)
    (hm : m = (2 ^ f) ^ 12 * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 2 - 1))) : C2Shape m := by
  have hfin := fin_D4 hf hm
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hodd8 : Odd (q ^ 8 + q ^ 4 + 1) := by
    have e8 : Even (q ^ 8) := (Nat.even_pow' (by norm_num)).mpr hev
    have e4 : Even (q ^ 4) := (Nat.even_pow' (by norm_num)).mpr hev
    exact (e8.add e4).add_one
  have hB := (hodd8.mul (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 6))).mul
    (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 2))
  have h68 : q ^ 6 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h28 : q ^ 2 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  refine ⟨hfin, ?_, f, 12, 1, ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)), q ^ 8 + q ^ 4 + 1,
    by omega, by norm_num, Or.inl rfl, ?_, hB, ?_, ?_, ?_⟩
  · rw [hm]
    exact Dvd.dvd.mul_left (h2f.mul_left _) _
  · rw [mul_one, pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h48 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ (3 * q ^ 8) * q ^ 6 * q ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (by have := Nat.one_le_pow 8 q (by omega); omega)
        (Nat.sub_le _ _)) (Nat.sub_le _ _)
    have h2 : (3 * q ^ 8) * q ^ 6 * q ^ 2 = 3 * q ^ 16 := by ring
    have h3 : q ^ 24 = q ^ 8 * q ^ 16 := by ring
    have h4 : 2 ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hq4 8
    have h5 : 1 ≤ q ^ 16 := Nat.one_le_pow _ _ (by omega)
    have h6 : 2 ^ 8 * q ^ 16 ≤ q ^ 8 * q ^ 16 := Nat.mul_le_mul_right _ h4
    show _ < q ^ (2 * 12) - 1
    rw [show 2 * 12 = 24 by norm_num]
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · exact Nat.le_of_dvd (by positivity) h'
      · have := Nat.le_of_dvd (by have := two_le_pow_of_two_le hq4 (by norm_num : 1 ≤ 6); omega) h'
        omega
    · have := Nat.le_of_dvd (by have := two_le_pow_of_two_le hq4 (by norm_num : 1 ≤ 2); omega) h
      omega
  · rw [pow_mul, ← hq]
    have h4 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h12 : q ^ 12 = q ^ 4 * q ^ 8 := by ring
    have h16 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq4 4
    have h5 : 2 ^ 4 * q ^ 8 ≤ q ^ 4 * q ^ 8 := Nat.mul_le_mul_right _ h16
    have h6 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega

theorem c2Shape_F4 {f m : ℕ} (hf : 3 ≤ f)
    (hm : m = (2 ^ f) ^ 12 * (((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) *
      (2 ^ f - 1))) : C2Shape m := by
  have hfin := fin_F4 hf hm
  obtain ⟨hev, hq4⟩ := two_pow_facts hf (by omega)
  have h2f := three_dvd_sq_sub_one f
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hev hq4 hm h2f
  norm_num at hq4
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hB := (((odd_pow_add_one_of_even hev (by norm_num : 1 ≤ 6)).mul
    (odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 4))).mul
    (odd_pow_add_one_of_even hev (by norm_num : 1 ≤ 3))).mul
    (by simpa using odd_pow_sub_one_of_even hev hq1 (by norm_num : 1 ≤ 1))
  have h3 : 3 ∣ q ^ 4 - 1 := by
    rw [four_sub_one_eq hq1]
    exact h2f.mul_right _
  have h36 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h46 : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h16 : q ≤ q ^ 6 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  refine ⟨hfin, ?_, f, 12, 1, ((q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)), q ^ 6 + 1,
    by omega, by norm_num, Or.inl rfl, ?_, hB, ?_, ?_, ?_⟩
  · rw [hm]
    exact Dvd.dvd.mul_left ((((h3.mul_left _).mul_right _).mul_right _)) _
  · rw [mul_one, pow_mul, ← hq]
    exact hm
  · rw [four_pow_eq, ← hq]
    have h1 : (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤
        (2 * q ^ 6) * q ^ 4 * (2 * q ^ 3) * q :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
        (by have := Nat.one_le_pow 6 q (by omega); omega) (Nat.sub_le _ _))
        (by have := Nat.one_le_pow 3 q (by omega); omega)) (Nat.sub_le _ _)
    have h2 : (2 * q ^ 6) * q ^ 4 * (2 * q ^ 3) * q = 4 * q ^ 14 := by ring
    have h24 : q ^ 24 = q ^ 10 * q ^ 14 := by ring
    have h4 : 2 ^ 10 ≤ q ^ 10 := Nat.pow_le_pow_left (by omega) 10
    have h5 : 1 ≤ q ^ 14 := Nat.one_le_pow _ _ (by omega)
    have h6 : 2 ^ 10 * q ^ 14 ≤ q ^ 10 * q ^ 14 := Nat.mul_le_mul_right _ h4
    show _ < q ^ (2 * 12) - 1
    rw [show 2 * 12 = 24 by norm_num]
    omega
  · intro p hp hpB
    rcases (Nat.Prime.dvd_mul hp).mp hpB with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
      · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
        · exact Nat.le_of_dvd (by positivity) h''
        · have := Nat.le_of_dvd
            (by have := two_le_pow_of_two_le (by omega : 2 ≤ q) (by norm_num : 1 ≤ 4); omega) h''
          omega
      · have := Nat.le_of_dvd (by positivity) h'
        omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  · rw [pow_mul, ← hq]
    have h12 : q ^ 12 = q ^ 6 * q ^ 6 := by ring
    have h8 : 8 ≤ q ^ 6 := le_trans hq4 h16
    have h7 : 8 * q ^ 6 ≤ q ^ 6 * q ^ 6 := Nat.mul_le_mul_right _ h8
    omega

end CFSG.Quasithin.Ch1Four
