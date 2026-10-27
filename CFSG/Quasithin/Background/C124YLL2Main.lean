module

public import CFSG.Quasithin.Background.C124YLCore
public import CFSG.Quasithin.Background.C124YLL2Hoff
public import CFSG.Quasithin.Background.C124Interface

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

namespace YL.L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

theorem package : Package Xs Ls U Z C.Kroot Ls := by
  refine ⟨C.Kroot_le, C.woff_Kroot, C.tight_Kroot, ?_, le_rfl, C.Kroot_sylow, ?_,
    C.moves_Kroot, ?_⟩
  · intro x hx ⟨k, hk⟩ _ hfix
    have hk' : (⟨x, hx⟩ : ↥Xs) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    exact C.cent_Kroot hk' hfix
  · exact ⟨F, inferInstance, inferInstance, C.hF4,
      ⟨(MulEquiv.ofBijective C.θ ⟨C.θ_inj, C.θ_surj⟩).symm⟩⟩
  · exact (sup_eq_left.2 inf_le_left).symm

end YL.L2Ctx

section Build

variable {G : Type} [Group G] [Finite G]

theorem YL.of_caseL2 {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (E : Entry X T V L R m hV) (h : CaseL2 hV L m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (YL.L2Ctx F (autI hV X) (autI hV L) (commV (autI hV L))
        (fixV (autI hV L) ⊓ commV (autI hV L))) := by
  obtain ⟨-, F, iF, fF, hF4, π, hR, hinj⟩ := h
  have hsec : ∀ q : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).Amb,
      q ∈ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).sec :=
    fun _ => Subgroup.mem_top _
  have hker : ∀ q ∈ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).ker, q = 1 :=
    fun q hq => Subgroup.mem_bot.1 hq
  obtain ⟨c, hc, hequiv⟩ := YL.coord_of_realizes hsec hker hR
  let e := specialLinearGroupEquivStatedSL 2 F
  have hLX : autI hV L ≤ autI hV X := autI_mono hV (le_of_mem_cComp E.comp)
  have hnorm : ∀ x ∈ autI hV X, x ∈ Subgroup.normalizer
      (autI hV L : Set (MulAut (IntMod V hV))) :=
    fun x hx => L2.autI_le_normalizer_of_le_normalizer hV E.normal hx
  refine ⟨F, iF, fF, ⟨?_⟩⟩
  exact
    { hF4 := hF4
      θ := π.comp e.toMonoidHom
      θ_inj := hinj.comp e.injective
      θ_surj := hR.1.comp e.surjective
      c := c
      coord := hc
      hLX := hLX
      hnorm := hnorm
      hU := fun x hx => (YL.sec_stable (hnorm x hx)).1
      hZ := fun x hx => (YL.sec_stable (hnorm x hx)).2
      equiv := fun s u hu => by
        exact hequiv (e s) u hu
      hFstar := E.fstarX }

end Build

theorem spec4bL2_holds : Spec4bL2 := by
  intro G _ _ X T V L R m hV E hc
  obtain ⟨F, iF, fF, ⟨C⟩⟩ := YL.of_caseL2 E hc
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := E.red.2.1
  have hRX : R ≤ X := E.RT.trans E.sylow.1
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hVR : V ≤ R := (le_pCoreOf_of_reduced E.red).trans E.QR
  refine YL.starL2_of_package E (Pk := autI hV X) (P0 := C.Kroot) (K0 := C.Kroot)
    (Y0 := autI hV L) (autI_mono hV hRX) ?_ C.Kroot_sylow ?_ ?_ C.package
  · intro l hl x hx
    have hlX := C.hLX hl
    exact (autI hV X).mul_mem ((autI hV X).mul_mem ((autI hV X).inv_mem hlX) hx) hlX
  · intro B hB hw
    exact C.eq_Kroot_of_woff hB hw
  · intro B hB
    obtain ⟨hw, hBR⟩ := YL.woff_of_mem_offenderImages hV hVR hRN _ _ hB
    exact C.woff_le_Ls (hBR.trans (autI_mono hV hRX)) hw

end CFSG.Quasithin.C124
