module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Ker7Direct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3GapMV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10OutFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case4Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16t_two_lt_mBar_of_case4_seven (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L 7 r) : 2 < mBar D.M V₀ V hV :=
  s16t_two_lt_mParam_of_case4_seven (s15_Infra_vtil_sq_eq_one V₀ V hV) hr h4At.1
    (s16n9b_case4_pcore D hV hc (by norm_num) hr h4At.1) h4At.2.1

theorem s16t_k_lt_mBar_of_case4 (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L p r) : D.k < mBar D.M V₀ V hV := by
  rcases hp with rfl | rfl
  · have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219 h4At.2.2
    have h1 := s16t_one_lt_mBar_of_three D h1217 h153 hc
    omega
  · have h2 := s16t_two_lt_mBar_of_case4_seven D hc hr h4At
    have hk := s16c167_k_le_two D
    omega

section Certified


theorem s16t_no_calOStar_of_case4_seven (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L 7 r) (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, hk, hA3, hA4, -⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  exact s16t_false_of_direct_seven (s15_Infra_vtil_sq_eq_one V₀ V hV) hr h4At.1
    (s16n9b_case4_pcore D hV hc (by norm_num) hr h4At.1) h4At.2.1 hBM hB1 hB2 hUt
    (hk.trans (s16c167_k_le_two D)) hA3 hA4

theorem s16t_no_calOStar_of_case4 (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 1 < r) (hr3 : r ≤ 3) (h32 : ¬ (p = 3 ∧ r = 2))
    (h4At : Case168_4At D V₀ V hV L p r) (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  rcases hp with rfl | rfl
  · obtain rfl : r = 3 := by omega
    exact s16c1610_no_calOStar_of_case4_three D hin hc h4At g
  · exact s16t_no_calOStar_of_case4_seven D hc hr h4At g

end Certified

section CertifiedOut


theorem s16t_out10_of_case168_4_three (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    (h153 : R15_3Small D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L p r) : Out10 D V₀ V hV := by
  by_cases h32 : p = 3 ∧ r = 2
  · obtain ⟨rfl, rfl⟩ := h32
    exact s16c1610_out10_of_case4_two_three D hin hc h4At
  · have hkm := s16t_k_lt_mBar_of_case4 D hin h1217 h153 hc hp hr h4At
    by_cases hr3 : r ≤ 3
    · exact s16c1610_out10_of_no_calOStar D hin.hx hin.h61 hin.h127 hin.h1114 hin.h162
        hc.setting.hyp16.hyp125 hkm
        (fun _ g => s16t_no_calOStar_of_case4 D hin hc hp hr hr3 h32 h4At g)
    · exact s16c1610_out10_of_case4_big D hin hc hp (by omega) h4At hkm

end CertifiedOut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
