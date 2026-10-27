module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.Component
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.FFMulAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.Offender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.Reduced
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c4Holds.Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin

theorem w4Thm12McClurg_of
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) : W4Thm12McClurg := by
  intro G _ _ M T V L hK hT hV hR hL hLV hJ
  have hVe : IsElemAbelian 2 V := hV.2.2.2
  have hP := McClurg.pCoreOf_le_centralizer hV hR
  obtain ⟨A, hA, hxa⟩ := McClurg.exists_isMaxElemAbelian_not_mem hT hL hJ
  have hLA := McClurg.commutator_autI_ne_bot hVe hV.2.2.1 hP hL hLV hA.1 hxa
  have hAne : autI hVe A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.commutator_bot_right] at hLA
    exact hLA rfl
  have hc := McClurg.ffConclusion_of_mulAut_of_commutator_ne_bot hFF IntMod.sq_eq_one
    (McClurg.isKGroup_autI hVe hV.2.2.1 hK) (McClurg.pCoreOf_autI_eq_bot hV hR hVe)
    (McClurg.isFFStarOffender_autI hVe hV.2.1 hV.2.2.1 hA hAne)
    (McClurg.isComponentOf_autI hVe hV.2.2.1 hP hL hLV) hLA
  obtain ⟨e⟩ := McClurg.nonempty_centerQuot_autI_equiv hVe hV.2.2.1 hP hL hLV
  exact McClurg.classicalEvenAltG2Der_of_ffConclusion (McClurg.isQuasisimple_bar2 hL)
    (McClurg.odd_card_center_bar2 L)
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffConclusion_of_mulEquiv e hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
