module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import Certificates.Certificate4212

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint
open CFSG.Sporadic.Mathieu (m11a m11b m12a m12b m22a m22b card_M11 card_M12 card_M22 m11_hyp
  m12_hyp m22_hyp)

theorem cent2NoComp_m11 :
    Cent2NoComp ↥NativeSporadic.M11 := by
  have hcert : BaseCertS 11 (List.range 11)
      (slpTabsA (tab 11 m11a).toArray (tab 11 m11b).toArray m11Prog) m11Qp
      159 189 193 191 195 m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 := by
    rw [m11_tab_a, m11_tab_b]
    exact m11_cert
  obtain ⟨S, z₀, hSk, hz2, hZ, hzT⟩ := centre_data_of_baseCertS (n := 11) (List.range 11)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m11a m11b m11Prog m11_valid m11Qp
    159 189 193 191 195 m11Enum.1 m11Enum.2.1 m11Enum.2.2 4 (by norm_num) hcert
  have hΓ : Nat.card ↥NativeSporadic.M11 = 2 ^ 4 * 495 := by rw [card_M11]; norm_num
  have hzT' : (tab 11 z₀).toArray = m11SLP[159]! := by
    rw [hzT, m11_tab_a, m11_tab_b]
    rfl
  exact cent2NoComp_of_class_only (n := 11) m11_hyp.gen (isSylowTwoOf_of_card (by decide) hSk hΓ)
    hz2 hZ hzT' (by rw [m11_tab_a]) (by rw [m11_tab_b])
    Certificates.certificate4212.1 (by decide) hΓ hSk (by rw [card_M11]; norm_num)

theorem cent2NoComp_m12 :
    Cent2NoComp ↥NativeSporadic.M12 := by
  have hcert : BaseCertS 12 (List.range 12)
      (slpTabsA (tab 12 m12a).toArray (tab 12 m12b).toArray m12Prog) m12Qp
      153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 := by
    rw [m12_tab_a, m12_tab_b]
    exact m12_cert
  obtain ⟨S, z₀, hSk, hz2, hZ, hzT⟩ := centre_data_of_baseCertS (n := 12) (List.range 12)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m12a m12b m12Prog m12_valid m12Qp
    153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 (by norm_num) hcert
  have hΓ : Nat.card ↥NativeSporadic.M12 = 2 ^ 6 * 1485 := by rw [card_M12]; norm_num
  have hzT' : (tab 12 z₀).toArray = m12SLP[153]! := by
    rw [hzT, m12_tab_a, m12_tab_b]
    rfl
  exact cent2NoComp_of_class_only (n := 12) m12_hyp.gen (isSylowTwoOf_of_card (by decide) hSk hΓ)
    hz2 hZ hzT' (by rw [m12_tab_a]) (by rw [m12_tab_b])
    Certificates.certificate4212.2.1 (by decide) hΓ hSk (by rw [card_M12]; norm_num)

theorem cent2NoComp_m22 :
    Cent2NoComp ↥NativeSporadic.M22 := by
  have hcert : BaseCertS 22 (List.range 22)
      (slpTabsA (tab 22 m22a).toArray (tab 22 m22b).toArray m22Prog) m22Qp
      163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 := by
    rw [m22_tab_a, m22_tab_b]
    exact m22_cert
  obtain ⟨S, z₀, hSk, hz2, hZ, hzT⟩ := centre_data_of_baseCertS (n := 22) (List.range 22)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m22a m22b m22Prog m22_valid m22Qp
    163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 (by norm_num) hcert
  have hΓ : Nat.card ↥NativeSporadic.M22 = 2 ^ 7 * 3465 := by rw [card_M22]; norm_num
  have hzT' : (tab 22 z₀).toArray = m22SLP[163]! := by
    rw [hzT, m22_tab_a, m22_tab_b]
    rfl
  exact cent2NoComp_of_class_only (n := 22) m22_hyp.gen (isSylowTwoOf_of_card (by decide) hSk hΓ)
    hz2 hZ hzT' (by rw [m22_tab_a]) (by rw [m22_tab_b])
    Certificates.certificate4212.2.2 (by decide) hΓ hSk (by rw [card_M22]; norm_num)

end CFSG.Quasithin.E6.Spor
