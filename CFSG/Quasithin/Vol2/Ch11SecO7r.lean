module

public import CFSG.Quasithin.Vol2.Ch11SecO7q
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem profile_l3 {n N : ℕ} (hn : 2 ≤ n)
    (hN : N * Nat.gcd 3 (2 ^ n - 1) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) :
    Profile N (3 * n) ((((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / Nat.gcd 3 (2 ^ n - 1)) := by
  obtain ⟨-, hodd, h3, h315, hlt⟩ := profile_sl3 (N := (2 ^ n) ^ 3 *
    (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) hn rfl
  have hs := four_le_two_pow hn
  generalize hU : ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) = U at hodd h3 h315 hlt hN ⊢
  have hg3 : Nat.gcd 3 (2 ^ n - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hgU : Nat.gcd 3 (2 ^ n - 1) ∣ U := by
    rw [← hU]
    refine Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans ?_) _
    exact Nat.sub_one_dvd_pow_sub_one _ 3
  have hg0 : 0 < Nat.gcd 3 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨w, hw⟩ := hgU
  have hwU : U / Nat.gcd 3 (2 ^ n - 1) = w := by rw [hw, Nat.mul_div_cancel_left _ hg0]
  rw [hwU]
  have ea : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have hwodd : Odd w := by
    rw [hw] at hodd
    exact (Nat.odd_mul.mp hodd).2
  refine ⟨?_, hwodd, ?_, ?_, ?_⟩
  · rw [ea]
    apply Nat.eq_of_mul_eq_mul_right hg0
    rw [hN, hw]
    ring
  · rcases (Nat.dvd_prime Nat.prime_three).mp hg3 with hg | hg
    · rw [hg, one_mul] at hw
      exact hw ▸ h3
    ·
      have h31 : 3 ∣ 2 ^ n - 1 := hg ▸ Nat.gcd_dvd_right 3 (2 ^ n - 1)
      have h9 : 3 * 3 ∣ U := by
        rw [← hU]
        exact Nat.mul_dvd_mul (h31.trans (Nat.sub_one_dvd_pow_sub_one _ 2))
          (h31.trans (Nat.sub_one_dvd_pow_sub_one _ 3))
      rw [hw, hg] at h9
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
  ·
    have h945 : 945 ≤ U := by
      rw [← hU]
      have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 :=
        le_pow_sub_one ((by norm_num : 15 + 1 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left hs 2))
      have h3' : 63 ≤ (2 ^ n) ^ 3 - 1 :=
        le_pow_sub_one ((by norm_num : 63 + 1 ≤ 4 ^ 3).trans (Nat.pow_le_pow_left hs 3))
      exact (by norm_num : 945 ≤ 15 * 63).trans (Nat.mul_le_mul h2 h3')
    have hgle : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) hg3
    have : U ≤ Nat.gcd 3 (2 ^ n - 1) * w := hw.le
    have : Nat.gcd 3 (2 ^ n - 1) * w ≤ 3 * w := Nat.mul_le_mul_right _ hgle
    omega
  · have : w ≤ U := by
      rw [hw]
      exact Nat.le_mul_of_pos_left _ hg0
    omega


theorem list2_profile {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n) (h : List11_1_1Two X n) :
    ∃ A u, Profile (Nat.card X) A u ∧
      ((A = 3 * n ∧ (IsSL3 (2 ^ n) X ∨ IsPSL 3 2 n X)) ∨ A = 4 * n ∨ A = 6 * n ∨ A = 12 * n) := by
  rcases h with h | h | h | h | h | h | ⟨⟨m, rfl⟩, h⟩
  · refine ⟨3 * n, _, profile_sl3 hn ?_, Or.inl ⟨rfl, Or.inl h⟩⟩
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      3 K).symm).toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num),
      hK, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  · exact ⟨3 * n, _, profile_l3 hn (SecA.C11P9B.card_mul_gcd_of_isPSL3' (X := X) h),
      Or.inl ⟨rfl, Or.inr h⟩⟩
  · refine ⟨4 * n, _, profile_sp4 hn ?_, Or.inr (Or.inl rfl)⟩
    have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (by omega)).mpr even_two) odd_one)
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two
      (h : StatedClassicalModel X .PSp 2 2 n)).2.2.1 rfl, ordBC, hg, Nat.div_one,
      show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  · refine ⟨6 * n, _, profile_g2 hn ?_, Or.inr (Or.inr (Or.inl rfl))⟩
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 h.2, ordG2]
    ring
  · exact ⟨12 * n, _, profile_f4 (by omega)
      (CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h), Or.inr (Or.inr (Or.inr rfl))⟩
  · exact ⟨12 * n, _, profile_d4 (by omega)
      (CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two (by omega) h.2),
      Or.inr (Or.inr (Or.inr rfl))⟩
  · rw [show 3 * m / 3 = m by omega] at h
    exact ⟨12 * m, _, profile_d4 (by omega)
      (CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two (by omega) h.2),
      Or.inr (Or.inl (by ring))⟩

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
