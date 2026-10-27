module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectThree
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_no_calOStar_of_case4_seven (D : Data G) (hin : In10 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) {r : ℕ} (hr : 1 < r)
    (h4At : Case168_4At D V₀ V hV L 7 r) (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, hk, hA3, hA4, -⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  have hge := s16c1610_three_le_pRank_mBar_of_four D hin.hx hin.h61 hin.h127
    hc.setting.hyp16 hV h4 h4At.2.2
  exact s16c1610_false_of_direct_seven (s15_Infra_vtil_sq_eq_one V₀ V hV) hr h4At.1
    (s16n9b_case4_pcore D hV hc (by norm_num) hr h4At.1) h4At.2.1 hge hBM hB1 hB2 hUt
    (hk.trans (s16c167_k_le_two D)) hA3 hA4

theorem s16c1610_no_calOStar_of_case4_three (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h4At : Case168_4At D V₀ V hV L 3 3) (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, hk, hA3, hA4, hA5⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219 h4At.2.2
  exact s16c1610_false_of_direct_three (s15_Infra_vtil_sq_eq_one V₀ V hV) h4At.1
    (s16n9b_case4_pcore D hV hc (by norm_num) (by norm_num) h4At.1)
    (s16c1610_lBar_normal_of_case4_three D hc h4At) h4At.2.1 hBM hB1 hB2 hUt
    (hk.trans hk1.le) hA3 hA4 hA5

theorem s16c1610_no_calOStar_of_case4_four (D : Data G) (hin : In10 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r) (hr3 : r ≤ 3)
    (h32 : ¬ (p = 3 ∧ r = 2)) (h4At : Case168_4At D V₀ V hV L p r) (g : G) :
    ¬ InCalOStar D.k D.M V₀ V g := by
  rcases hp with rfl | rfl
  · obtain rfl : r = 3 := by omega
    exact s16c1610_no_calOStar_of_case4_three D hin hc h4At g
  · exact s16c1610_no_calOStar_of_case4_seven D hin h4 hc hr h4At g

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
