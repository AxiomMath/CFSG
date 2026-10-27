module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvPerm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtZPInvCore

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Mathieu (m12a m12b m22a m22b m24a m24b card_M12 card_M22 card_M24
  fam_m12_simplicity fam_m22_simplicity fam_m23_simplicity fam_m24_simplicity)
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card)

theorem zpUniq_m12 :
    ZPUniq ↥M12 := by
  obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 12) (List.range 12)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m12a m12b m12Prog m12_valid m12Qp
    153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 1485
    (by rw [card_M12]; norm_num) (by decide) (by rw [m12_tab_a, m12_tab_b]; exact m12_cert)
  exact zpUniq_of_central_subset (center_eq_bot_of_simple fam_m12_simplicity.2.2
    (card_M12 : Nat.card ↥M12 = 95040) (by norm_num) (by norm_num)) Q hQ2 hQi z hQc

theorem zpUniq_m22 :
    ZPUniq ↥M22 := by
  obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 22) (List.range 22)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m22a m22b m22Prog m22_valid m22Qp
    163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 3465
    (by rw [card_M22]; norm_num) (by decide) (by rw [m22_tab_a, m22_tab_b]; exact m22_cert)
  exact zpUniq_of_central_subset (center_eq_bot_of_simple fam_m22_simplicity.2.2
    (card_M22 : Nat.card ↥M22 = 443520) (by norm_num) (by norm_num)) Q hQ2 hQi z hQc

theorem zpUniq_m23 :
    ZPUniq ↥M23 := by
  obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 23) (List.range 23)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m23GenA m23GenB m23Prog m23_valid m23Qp
    159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 79695
    (by rw [m23_card]; norm_num) (by decide) (by rw [m23_tab_a, m23_tab_b]; exact m23_cert)
  exact zpUniq_of_central_subset (center_eq_bot_of_simple fam_m23_simplicity.2.2
    (m23_card : Nat.card ↥M23 = 10200960) (by norm_num) (by norm_num)) Q hQ2 hQi z hQc

theorem zpUniq_m24 :
    ZPUniq ↥M24 := by
  obtain ⟨Q, z, hQ2, hQi, hQc⟩ := sylow_center_of_baseCertS (n := 24) (List.range 24)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m24a m24b m24Prog m24_valid m24Qp
    162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 239085
    (by rw [card_M24]; norm_num) (by decide) (by rw [m24_tab_a, m24_tab_b]; exact m24_cert)
  exact zpUniq_of_central_subset (center_eq_bot_of_simple fam_m24_simplicity.2.2
    (card_M24 : Nat.card ↥M24 = 244823040) (by norm_num) (by norm_num)) Q hQ2 hQi z hQc

end CFSG.Quasithin.ZPInv
