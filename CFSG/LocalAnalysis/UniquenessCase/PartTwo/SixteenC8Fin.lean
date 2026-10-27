module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Spin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_mbar_eq_lbar (D : Data G) (h1217 : R1217 D) (hA : RSp6SmallMod)
    (hC : RSp6SpinCent) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_8 D V₀ V hV L) :
    Mbar D.M V₀ V hV = lBar V₀ V hV L := by
  obtain ⟨hrk, hirr, hN⟩ := c8_spin_module D h1217 hA hS hc
  exact c8_eq_of_map_conj_eq (s15_Infra_vtil_sq_eq_one V₀ V hV) hC hc.1 hrk hirr
    (barSub_mono V₀ V hV hS.setting.hyp151.le) hN

theorem r16_26_fin_holds (D : Data G) (h1217 : R1217 D) (hA : RSp6SmallMod)
    (hC : RSp6SpinCent) (hF : RSp6SpinForm) (hSt : RSp6SpinStab) : R16_26_fin D := by
  intro V₀ V L hV hS hc
  obtain ⟨hrk, hirr, -⟩ := c8_spin_module D h1217 hA hS hc
  have hW := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hM := c8_mbar_eq_lbar D h1217 hA hC hS hc
  refine ⟨hF _ hW _ hc.1 hrk hirr, fun Q hQ hQi => ?_⟩
  rw [hM]
  exact hSt _ hW _ hc.1 hrk hirr Q hQ hQi

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
