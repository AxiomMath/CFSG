module

public import CFSG.LocalAnalysis.UniquenessCase.UCK898b
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Y
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec4.Item434U38

section Certificates


theorem nonempty_equiv_psu38_of_isU3 {X : Type} [Group X] (hU : IsU3 (X ⧸ center X) 3) :
    Nonempty ((X ⧸ center X) ≃* ↥X') := by
  have hcl : CFSG.Open.StatedClassicalModel (X ⧸ center X) .PSU 3 2 3 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide)
  obtain ⟨e⟩ : Nonempty ((X ⧸ center X) ≃* CFSG.PGLModel.projSU 3 2 3) :=
    CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ (MulEquiv.refl _))
  exact nonempty_equiv_X' ⟨e⟩

theorem u3E9Cover_of_certs (hCen : U3Center) : U3E9Cover := by
  intro X _ _ hX z hz
  obtain ⟨φ⟩ := nonempty_equiv_psu38_of_isU3 (X := X) hX.2
  obtain ⟨t, ht⟩ := exists_orderOf_three_psu38
  exact u3E9Cover_of_Y (hCen X 3 hX) (YCoverPlus.of_mulEquiv φ yCoverPlus_psu38)
    ⟨φ.symm t, by rw [MulEquiv.orderOf_eq]; exact ht⟩ z hz

theorem u3Fix3Inner_of_certs (hCen : U3Center) : U3Fix3Inner := by
  intro X _ _ hX α hα hin
  obtain ⟨φ⟩ := nonempty_equiv_psu38_of_isU3 (X := X) hX.2
  obtain ⟨t, ht⟩ := exists_orderOf_three_psu38
  exact u3Fix3Inner_of_Y (hCen X 3 hX) (YFix3Wit.of_mulEquiv φ yFix3Wit_psu38)
    ⟨φ.symm t, by rw [MulEquiv.orderOf_eq]; exact ht⟩ α hα hin

theorem u3E9Fix_of_certs (hCen : U3Center) : U3E9Fix := by
  intro X _ _ hX x hx β hβ hβx
  obtain ⟨φ⟩ := nonempty_equiv_psu38_of_isU3 (X := X) hX.2
  obtain ⟨t, ht⟩ := exists_orderOf_three_psu38
  exact u3E9Fix_of_Y hX.1.1 (hCen X 3 hX) (YCoverPlus.of_mulEquiv φ yCoverPlus_psu38)
    (YFixClaim.of_mulEquiv φ yFixClaim_psu38) ⟨φ.symm t, by rw [MulEquiv.orderOf_eq]; exact ht⟩ x hx β hβ hβx

theorem u3Trio_of_griess (hG : CFSG.Open.GriessAllModelsStatement) :
    U3Fix3Inner ∧ U3E9Cover ∧ U3E9Fix :=
  ⟨u3Fix3Inner_of_certs (u3Center_of_griess hG), u3E9Cover_of_certs (u3Center_of_griess hG),
    u3E9Fix_of_certs (u3Center_of_griess hG)⟩

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UCK
