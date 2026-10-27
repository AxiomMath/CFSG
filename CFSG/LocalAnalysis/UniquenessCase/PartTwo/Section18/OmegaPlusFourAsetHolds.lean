module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourAset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

theorem k_Omega4Plus_aParam_le_holds : K_Omega4Plus_aParam_le := by
  intro W _ _ X n hn _ hnat
  obtain ⟨S, hS, hK⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_omegaModel_of_natOmegaPlus hn hnat
  apply CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty
  intro A hA
  have h := S.aSet_succ_eq_empty hK (X := Subgroup.normalizer (X : Set (MulAut W)))
    (by rw [hS])
  rw [h] at hA
  exact hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
