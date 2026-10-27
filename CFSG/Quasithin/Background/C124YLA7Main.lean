module

public import CFSG.Quasithin.Background.C124YLCore
public import CFSG.Quasithin.Background.C124YLA7Pkg
public import CFSG.Quasithin.Background.C124YLA7Norm
public import CFSG.Quasithin.Background.C124Interface

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246.C123

theorem spec4bA7Four_holds : Spec4bA7Four := by
  intro G _ _ X T V L R m hV E hc
  obtain ⟨-, ⟨α, π, hπ⟩, -⟩ := hc
  let C : YL.A7.A7Ctx (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) := ⟨α, π, hπ⟩
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  have hLX : autI hV L ≤ autI hV X := autI_mono hV (le_of_mem_cComp E.comp)
  have hnormX : ∀ x ∈ autI hV X,
      x ∈ Subgroup.normalizer (autI hV L : Set (MulAut (IntMod V hV))) :=
    fun x hx => L2.autI_le_normalizer_of_le_normalizer hV E.normal hx
  have hstab := fun x (hx : x ∈ autI hV X) => YL.sec_stable (hnormX x hx)
  have hXL : autI hV X ≤ autI hV L :=
    C.le_Ls_of_normalizes hLX hnormX E.fstarX (fun x hx => (hstab x hx).1)
      (fun x hx => (hstab x hx).2)
  have hRs : autI hV R ≤ autI hV L := (autI_mono hV hRX).trans hXL
  obtain ⟨K1, hK1⟩ := (offenderImages_nonempty_iff_not_le hV).2 E.hJ
  obtain ⟨hw1, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
    (fixV (autI hV L) ⊓ commV (autI hV L)) hK1
  have hex : ∃ K1, K1 ≤ autI hV L ∧
      YL.WOff (commV (autI hV L)) (fixV (autI hV L) ⊓ commV (autI hV L)) K1 :=
    ⟨K1, hBR.trans hRs, hw1⟩
  refine YL.starL2_of_package E (Pk := autI hV L) (P0 := sylowA.map C.phi)
    (K0 := kleinA.map C.phi) (Y0 := YL.A7.Yst.map C.phi) hRs ?_ C.sylow_P ?_ ?_
    (C.package (fun l hl => (hstab l (hLX hl)).1) (fun l hl => (hstab l (hLX hl)).2) hex)
  · intro l hl x hx
    exact (autI hV L).mul_mem ((autI hV L).mul_mem ((autI hV L).inv_mem hl) hx) hl
  · intro B hB hw
    exact C.unique_K hB hw
  · intro B hB
    obtain ⟨-, hBR'⟩ := YL.woff_of_mem_offenderImages hV hVR hRN (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) hB
    exact hBR'.trans hRs

end CFSG.Quasithin.C124
