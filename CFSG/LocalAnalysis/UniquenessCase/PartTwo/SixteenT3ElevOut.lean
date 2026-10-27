module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3ElevTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10OutFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10DirectSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16t_two_lt_mBar_of_case168_11 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h11 : Case168_11 D V₀ V hV L) :
    2 < mBar D.M V₀ V hV := by
  obtain ⟨hcyc, hrk, hs, -⟩ := h11
  have hodd : Odd (Nat.card ↥(barSub V₀ V hV L)) := by
    rw [show Nat.card ↥(barSub V₀ V hV L) = 7 from hcyc.2]
    decide
  obtain ⟨g, hg⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd hs
  have h3 := s16t_elev_three_le_mParam (s15_Infra_vtil_sq_eq_one V₀ V hV) hg hrk hcyc.2
  unfold mBar
  omega

section Certified


theorem s16t_no_calOStar_of_case168_11 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h11 : Case168_11 D V₀ V hV L)
    (g : G) : ¬ InCalOStar D.k D.M V₀ V g := by
  intro hO
  obtain ⟨Ut, B, hBM, hB1, hB2, hUt, -, -, hA4, -⟩ :=
    s16c1610_directData_of_calOStar D hc.setting.hyp16.hyp125 hO
  obtain ⟨hcyc, hrk, hs, -⟩ := h11
  have hodd : Odd (Nat.card ↥(barSub V₀ V hV L)) := by
    rw [show Nat.card ↥(barSub V₀ V hV L) = 7 from hcyc.2]
    decide
  obtain ⟨g', hg⟩ := s16t_twoConj_of_odd D h1217 hV hc hodd hs
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  exact hUt (s16c1610_ut_eq_top_of_card_le_two hT hB1 hB2
    (s16t_elev_card_le_two hT hg hrk hcyc.2 hBM hB2) hA4)

end Certified

section CertifiedOut


theorem s16t_out10_of_case168_11_three (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h11 : Case168_11 D V₀ V hV L) : Out10 D V₀ V hV := by
  have h2 := s16t_two_lt_mBar_of_case168_11 D h1217 hc h11
  have hk := s16c167_k_le_two D
  exact s16c1610_out10_of_no_calOStar D hin.hx hin.h61 hin.h127 hin.h1114 hin.h162
    hc.setting.hyp16.hyp125 (by omega)
    (fun _ g => s16t_no_calOStar_of_case168_11 D h1217 hc h11 g)

end CertifiedOut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
