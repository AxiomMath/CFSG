module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cF4Ord
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch11L2Q5cSzFF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem ordA_two_eq_formula (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]

theorem lt_ordA_two {k : ℕ} (hk : 3 ≤ k) : 20160 < ordA 2 (2 ^ k) := by
  rw [ordA_two_eq_formula]
  generalize hq : 2 ^ k = q
  have hq8 : 8 ≤ q := by
    rw [← hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hg : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h1 : 512 ≤ q ^ 3 :=
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq8 3
  have h2 : 63 ≤ q ^ 2 - 1 := by
    have : 64 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : 511 ≤ q ^ 3 - 1 := by omega
  have hnum : 20161 * 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    calc 20161 * 3 ≤ 512 * (63 * 511) := by norm_num
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  calc 20160 < 20161 := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 := (Nat.le_div_iff_mul_le (by norm_num)).mpr hnum
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := Nat.div_le_div_left hg3 hg

theorem lt_ordBC_two {k : ℕ} (hk : 2 ≤ k) : 20160 < ordBC 2 (2 ^ k) := by
  rw [CFSG.Timmesfeld.Orders.ordBC_two_eq (g := k) (by omega), pow_mul]
  generalize hq : 2 ^ k = q
  have hq4 : 4 ≤ q := by
    rw [← hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h1 : 256 ≤ q ^ 4 :=
    calc 256 = 4 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq4 4
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : 255 ≤ q ^ 4 - 1 := by omega
  calc 20160 < 256 * (15 * 255) := by norm_num
    _ ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

theorem three_dvd_card_isPSL3 {Y : Type} [Group Y] {k : ℕ} (h : IsPSL 3 2 k Y) :
    3 ∣ Nat.card Y := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).toEquiv]
  exact three_dvd_card_psl (by norm_num)

theorem isPSp4_of_isSp4Prime {Y : Type} [Group Y] {k : ℕ} (hk : 2 ≤ k)
    (h : E2.IsSp4Prime k Y) : IsPSp4 2 k Y := by
  unfold E2.IsSp4Prime at h
  split_ifs at h with hk1
  · omega
  · exact h

theorem ordA_one_ne_ordA_two {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ordA 1 (2 ^ n) ≠ ordA 2 (2 ^ k) := by
  intro heq
  obtain ⟨r, hr, h1⟩ : ∃ r, Odd r ∧ ordA 1 (2 ^ n) = 2 ^ (n * 1) * r :=
    (profile_ordA (n := 1) le_rfl hn).two
  obtain ⟨r', hr', h2⟩ : ∃ r, Odd r ∧ ordA 2 (2 ^ k) = 2 ^ (k * 3) * r :=
    (profile_ordA (n := 2) (by norm_num) (by omega)).two
  have hN : n * 1 = k * 3 := eq_of_two_pow_mul_odd hr hr' (h1.symm.trans (heq.trans h2))
  have hn3 : n = 3 * k := by omega
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := n * 2) (by omega) (by omega)
  have hp1 : p ∣ ordA 1 (2 ^ n) := prim_dvd_ordA (m := 1) (i := 2) hn le_rfl le_rfl hp
  rw [heq] at hp1
  obtain ⟨i, hi, hki⟩ := index_of_prim_dvd_ordA (m := 2) (by norm_num) hp (by omega) hp1
  simp only [Finset.mem_Icc] at hi
  have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hki
  have h3 : k * i ≤ k * 3 := Nat.mul_le_mul (le_refl k) hi.2
  rw [hn3] at hle
  nlinarith

theorem ordA_one_ne_ordSuzuki {n f : ℕ} (hn : 1 ≤ n) (hf : Odd f) :
    ordA 1 (2 ^ n) ≠ ordSuzuki (2 ^ f) := by
  intro heq
  obtain ⟨a, rfl⟩ := hf
  apply not_three_dvd_ordSuzuki_odd a
  rw [← heq, ordA_one_two_pow_eq hn]
  exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one n) _

theorem not_a312Out_of_isPSL3 {Y : Type} [Group Y] {k : ℕ}
    (hk : 3 ≤ k) (hY : IsPSL 3 2 k Y) : ¬ A312Out Y := by
  have hc : Nat.card Y = ordA 2 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl
  obtain ⟨r, hr, hr'⟩ : ∃ r, Odd r ∧ ordA 2 (2 ^ k) = 2 ^ (k * 3) * r :=
    (profile_ordA (n := 2) (by norm_num) (by omega)).two
  rintro (h | ⟨n, hn, h⟩ | ⟨f, h⟩ | ⟨p, hp, hp2, h⟩ | h | h)
  · have := lt_ordA_two hk
    omega
  · have hcn : Nat.card Y = ordA 1 (2 ^ n) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    exact ordA_one_ne_ordA_two (by omega) (by omega) (hcn.symm.trans hc)
  · obtain ⟨hodd, -, hcf⟩ := card_isSz h
    obtain ⟨a, rfl⟩ := hodd
    exact not_three_dvd_ordSuzuki_odd a (hcf ▸ three_dvd_card_isPSL3 hY)
  · exact false_of_isPSL3_of_card (by omega) hY hp hp2 h
  · rw [hc, hr', show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num] at h
    have := eq_of_two_pow_mul_odd hr ⟨1732, by norm_num⟩ h
    omega
  · rw [hc, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num] at h
    have := eq_of_two_pow_mul_odd hr ⟨119542, by norm_num⟩ h
    omega

theorem not_a312Out_of_isPSp4 {Y : Type} [Group Y] {k : ℕ}
    (hk : 2 ≤ k) (hY : IsPSp4 2 k Y) : ¬ A312Out Y := by
  have hc : Nat.card Y = ordBC 2 (2 ^ k) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hY).2.2.1 rfl
  obtain ⟨r, hr, hr'⟩ : ∃ r, Odd r ∧ ordBC 2 (2 ^ k) = 2 ^ (k * 4) * r :=
    (profile_ordBC (n := 2) (by omega)).two
  rintro (h | ⟨n, hn, h⟩ | ⟨f, h⟩ | ⟨p, hp, hp2, h⟩ | h | h)
  · have := lt_ordBC_two hk
    omega
  · have hcn : Nat.card Y = ordA 1 (2 ^ n) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    exact ordA_ne_ordBC_two le_rfl (by omega) (by omega) (hcn.symm.trans hc)
  · obtain ⟨hodd, -, hcf⟩ := card_isSz h
    exact ordSuzuki_ne_ordBC_two hodd (by omega) (hcf.symm.trans hc)
  · exact false_of_isPSp4_of_card hk hY hp hp2 h
  · rw [hc, hr', show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num] at h
    have := eq_of_two_pow_mul_odd hr ⟨1732, by norm_num⟩ h
    omega
  · rw [hc, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num] at h
    have := eq_of_two_pow_mul_odd hr ⟨119542, by norm_num⟩ h
    omega

theorem card_l2BadType_ne_m24 {Y : Type} [Group Y] {k : ℕ}
    (hk : 2 ≤ k) (hY : L2BadType k Y) : Nat.card Y ≠ 244823040 := by
  have h239 : Odd 239085 := ⟨119542, by norm_num⟩
  rcases hY with h | h | h | h
  · intro he
    exact not_three_dvd_card_isSz h (by rw [he]; norm_num)
  · obtain ⟨r, hr, hr'⟩ := exists_odd_ordTwistedA_two (k := k) (by omega)
    rw [card_isPSU3 h, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
    intro he
    have := eq_of_two_pow_mul_odd hr h239 he
    omega
  · have hc : Nat.card Y = ordA 2 (2 ^ k) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    obtain ⟨r, hr, hr'⟩ : ∃ r, Odd r ∧ ordA 2 (2 ^ k) = 2 ^ (k * 3) * r :=
      (profile_ordA (n := 2) (by norm_num) (by omega)).two
    rw [hc, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
    intro he
    have := eq_of_two_pow_mul_odd hr h239 he
    omega
  · have hc : Nat.card Y = ordBC 2 (2 ^ k) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two (isPSp4_of_isSp4Prime hk h)).2.2.1 rfl
    obtain ⟨r, hr, hr'⟩ : ∃ r, Odd r ∧ ordBC 2 (2 ^ k) = 2 ^ (k * 4) * r :=
      (profile_ordBC (n := 2) (by omega)).two
    rw [hc, hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
    intro he
    have := eq_of_two_pow_mul_odd hr h239 he
    omega

theorem card_l2BadType_ne_psl2 {Y : Type} [Group Y] {k m : ℕ}
    (hk : 2 ≤ k) (hm : 1 ≤ m) (hY : L2BadType k Y) : Nat.card Y ≠ ordA 1 (2 ^ (2 * m)) := by
  rcases hY with h | h | h | h
  · obtain ⟨hodd, -, hc⟩ := card_isSz h
    rw [hc]
    exact fun he => ordA_one_ne_ordSuzuki (by omega) hodd he.symm
  · rw [card_isPSU3 h]
    exact fun he => ordA_ne_ordTwistedA le_rfl (by omega) le_rfl (by omega) he.symm
  · have hc : Nat.card Y = ordA 2 (2 ^ k) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    rw [hc]
    exact fun he => ordA_one_ne_ordA_two (by omega) hk he.symm
  · have hc : Nat.card Y = ordBC 2 (2 ^ k) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two (isPSp4_of_isSp4Prime hk h)).2.2.1 rfl
    rw [hc]
    exact fun he => ordA_ne_ordBC_two le_rfl (by omega) (by omega) he.symm

theorem ordTwistedF4_ne_m24 {f : ℕ} (hf : 1 ≤ f) : ordTwistedF4 (2 ^ f) ≠ 244823040 := by
  obtain ⟨r, hr, hr'⟩ := (profile_ordTwistedF4 hf).two
  rw [hr', show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num]
  intro he
  have := eq_of_two_pow_mul_odd hr ⟨119542, by norm_num⟩ he
  omega

theorem not_ordA_one_dvd_m23 {m : ℕ} (hm : 2 ≤ m) : ¬ ordA 1 (2 ^ (2 * m)) ∣ 10200960 := by
  rw [ordA_one_two_pow_eq (n := 2 * m) (by omega),
    show (10200960 : ℕ) = 2 ^ 7 * 79695 by norm_num]
  intro h
  have h2 : 2 ^ (2 * m) ∣ 2 ^ 7 * 79695 := (dvd_mul_right _ _).trans h
  have h3 : 2 ^ (2 * m) ∣ 2 ^ 7 :=
    (Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 79695)).dvd_of_dvd_mul_right h2
  have h4 : 2 * m ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  have h5 : m ≤ 3 := by omega
  interval_cases m
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.Quasithin.Vol2.Ch11.SecB
