module

public import CFSG.Quasithin.Background.C124YLCore
public import CFSG.Quasithin.Background.C124YLA6Pkg
public import CFSG.Quasithin.Background.C124Interface

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

theorem spec4bAlt6b_holds : Spec4bAlt6b := by
  intro G _ _ X T V L R m hV E hc hRL
  obtain ⟨-, π, hR, hinj⟩ := hc
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp E.comp).trans hXN
  have hRs : autI hV R ≤ autI hV L := by
    have h1 := autI_mono hV hRL
    rw [autI_sup hV hLN (inf_le_left.trans hXN),
      autI_eq_bot_of_le_centralizer hV inf_le_right, sup_bot_eq] at h1
    exact h1
  refine YL.starL2_of_package E (Pk := autI hV L) (P0 := YL.A6.up π YL.A6.Pg)
    (K0 := YL.A6.up π YL.A6.Kg) (Y0 := YL.A6.up π YL.A6.Yg) hRs ?_ (YL.A6.sylow_P hR hinj) ?_ ?_
    (YL.A6.package hR hinj)
  · intro l hl x hx
    exact (autI hV L).mul_mem ((autI hV L).mul_mem ((autI hV L).inv_mem hl) hx) hl
  · intro B hB hw
    exact YL.A6.eq_up_Kg hR hinj hB hw
  · intro B hB
    obtain ⟨-, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) hB
    exact hBR.trans hRs

end CFSG.Quasithin.C124
