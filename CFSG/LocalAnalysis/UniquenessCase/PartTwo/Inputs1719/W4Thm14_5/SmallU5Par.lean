module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KCommon
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Adapters.LieModelOrders
import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem le_twenty_of_two_pow_mul_odd_dvd_u54 {a r : ℕ}
    (h : 2 ^ a * r ∣ 53443952640000) : a ≤ 20 := by
  have h1 : 2 ^ a ∣ 2 ^ 20 * 50968125 :=
    (Dvd.intro r rfl).trans (by rw [show (2 : ℕ) ^ 20 * 50968125 = 53443952640000 by norm_num]; exact h)
  have h2 := (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 50968125)).dvd_of_dvd_mul_right h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2

variable {X : Type} [Group X] {n : ℕ}

theorem eq_four_of_isL2_of_dvd_u54 (h : IsL2 X n) (hn : 2 < n)
    (hd : Nat.card X ∣ 53443952640000) : n = 4 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hd
  obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl (by omega : 1 ≤ n)).two
  change ordA 1 (2 ^ n) ∣ _ at hd
  have h20 := le_twenty_of_two_pow_mul_odd_dvd_u54 (hr ▸ hd)
  rw [show n * (1 * (1 + 1) / 2) = n by simp] at h20
  interval_cases n <;> first | rfl | (exfalso; revert hd; decide)

theorem false_of_isSz_of_dvd_u54 (h : IsSz X n) (hd : Nat.card X ∣ 53443952640000) : False := by
  obtain ⟨a, ha, rfl, hc⟩ := s208k_card_of_isSz h
  rw [hc] at hd
  have h20 := le_twenty_of_two_pow_mul_odd_dvd_u54 (a := 2 * (2 * a + 1))
    (r := ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) (by
      have : 2 ^ (2 * (2 * a + 1)) * (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) =
          ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
        rw [← pow_mul, mul_comm (2 * a + 1) 2]
        ring
      rw [this]
      exact hd)
  have ha4 : a ≤ 4 := by omega
  interval_cases a <;> revert hd <;> decide

theorem eq_four_of_isU3_of_dvd_u54 (h : IsU3 X n) (hn : 2 < n)
    (hd : Nat.card X ∣ 53443952640000) : n = 4 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hd
  obtain ⟨r, -, hr⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl (by omega : 1 ≤ n)).two
  change ordTwistedA 2 (2 ^ n) ∣ _ at hd
  have h20 := le_twenty_of_two_pow_mul_odd_dvd_u54 (hr ▸ hd)
  have hn6 : n ≤ 6 := by omega
  interval_cases n <;> first | rfl | (exfalso; revert hd; decide)

theorem eq_four_of_isL3_of_dvd_u54 (h : IsL3 X n) (hn : 2 < n)
    (hd : Nat.card X ∣ 53443952640000) : n = 4 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hd
  obtain ⟨r, -, hr⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) (by omega : 1 ≤ n)).two
  change ordA 2 (2 ^ n) ∣ _ at hd
  have h20 := le_twenty_of_two_pow_mul_odd_dvd_u54 (hr ▸ hd)
  have hn6 : n ≤ 6 := by omega
  interval_cases n <;> first | rfl | (exfalso; revert hd; decide)

theorem eq_four_of_isSp4_of_dvd_u54 (h : IsSp4 X n) (hn : 2 < n)
    (hd : Nat.card X ∣ 53443952640000) : n = 4 := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hd
  obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) (by omega : 1 ≤ n)).two
  change ordBC 2 (2 ^ n) ∣ _ at hd
  have h20 := le_twenty_of_two_pow_mul_odd_dvd_u54 (hr ▸ hd)
  have hn5 : n ≤ 5 := by omega
  interval_cases n <;> first | rfl | (exfalso; revert hd; decide)

theorem card_quot_center_dvd_of_dvd {N : ℕ} (hd : Nat.card X ∣ N) [Finite X] :
    Nat.card (X ⧸ Subgroup.center X) ∣ N :=
  (Subgroup.card_quotient_dvd_card _).trans hd

variable {G : Type} [Group G] [Finite G]

theorem eq_four_of_nParamSingle_of_dvd_u54 {Y : Type} [Group Y] [Finite Y]
    (h : NParamSingle Y n) (hn : 2 < n) (hd : Nat.card Y ∣ 53443952640000) : n = 4 := by
  rcases h with hSz | hL2 | hSU3 | hSL3 | hSp4
  · exact (false_of_isSz_of_dvd_u54 hSz hd).elim
  · exact eq_four_of_isL2_of_dvd_u54 hL2 hn hd
  · exact eq_four_of_isU3_of_dvd_u54 hSU3.2 hn (card_quot_center_dvd_of_dvd hd)
  · exact eq_four_of_isL3_of_dvd_u54 hSL3.2 hn (card_quot_center_dvd_of_dvd hd)
  · exact eq_four_of_isSp4_of_dvd_u54 hSp4 hn hd

theorem nParam_eq_four_of_isU5_two {L P : Subgroup G} (hS : IsU5 ↥L 2) (hPL : P ≤ L)
    (hN : NParam (Hinf P) n) (hn : 2 < n) : n = 4 := by
  have hcardL : Nat.card ↥L = 53443952640000 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_four
      (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))
  have hHP : Nat.card ↥(Hinf P) ∣ 53443952640000 :=
    hcardL ▸ Subgroup.card_dvd_of_le ((uc22p21c_Hinf_le P).trans hPL)
  rcases hN with hS1 | ⟨L₁, L₂, hL₁, -, -, -, hshapes⟩
  · exact eq_four_of_nParamSingle_of_dvd_u54 hS1 hn
      ((Subgroup.card_quotient_dvd_card _).trans hHP)
  · have hd : Nat.card (Bar2 L₁) ∣ 53443952640000 :=
      (Subgroup.card_quotient_dvd_card _).trans
        ((Subgroup.card_dvd_of_le hL₁.1.le).trans hHP)
    rcases hshapes L₁ (by simp) with hSz | hL2 | ⟨rfl, hSU3⟩
    · exact (false_of_isSz_of_dvd_u54 hSz hd).elim
    · exact eq_four_of_isL2_of_dvd_u54 hL2 hn hd
    · exact eq_four_of_isU3_of_dvd_u54 hSU3.2 hn (card_quot_center_dvd_of_dvd hd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
