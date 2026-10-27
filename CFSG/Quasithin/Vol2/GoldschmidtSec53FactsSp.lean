module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpExt
public import CFSG.Quasithin.Vol2.Ch5Sec3PerType
public import CFSG.Quasithin.Vol2.Ch5Sec3Facts533
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13.F431

theorem stmt5_3_3_factsAt_PSp (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (h532 : Stmt5_3_2At .PSp 2) : Stmt5_3_3_factsAt .PSp 2 := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨P, _, _, N₁, N₂, hT, hS, ⟨Φ⟩⟩ := exists_sp_facts hty
  obtain ⟨Y, _, hY, hE⟩ := h532 G T M L V H B D L₂ n f hyp hty hpar
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hE
  have : Finite Y := finite_of_lieModel_psp hY
  have hii := facts_ii Φ h527 hyp hty hT
  refine ⟨facts_i_of_ext h531 hyp hty hpar E (extFacts_sp hY E), hii.1, hii.2,
    fun _ u hu hord => ?_⟩
  refine facts_iii Φ h527 hyp hty hT hS u hu ?_
  rintro rfl
  rw [orderOf_one] at hord
  exact absurd hord (by norm_num)

end CFSG.Quasithin.H13.Sec53F
