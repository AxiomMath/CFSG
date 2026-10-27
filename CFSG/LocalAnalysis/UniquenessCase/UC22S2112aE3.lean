module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zk
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215SetupThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aU
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Gamma
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2d
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899E3
import CFSG.LocalAnalysis.UniquenessCase.UC22P20r

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedSolvableQ StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s21_12aF_of_s21_12aFR34 (hE : UC22P20gExcFacts) (hu38 : uc22p20oU38Witness)
    (hB : ListBNonabelian) (hO : LieOrderFormulasInput) (hThin : PartTwo.ThinList13)
    (hK : PartTwo.S17.K_LieModelNotL2) (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (h20_7 : S20_7 D) (h3 : S21_3 D Ch) (h5 : S21_5 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀) (hσ : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (h82 : F08.R82 D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (h74 : F07.R74Card D) (hR34 : S21_12aFR34 D (Choice214U D)) : S21_12aF D Ch :=
  s21_12aF_of_choice214U hE hu38 hB hO hThin hK h20_7 h3 hCh
    (s21_12aFU_of_residual hE h20_7 h5 hCh
      (s21_12aFR2_of_rest hGA hσ hKF7 (s21_12aFR2g_of_r74Card hGA hσ h74)
        (s21_12aFR2d_of_inputs hGA hσ h82 h76 h614 h74)) hR34)

theorem s21_12aF_dataOfSetup_of_s21_12aFR34 (hSQ : StronglyEmbeddedSolvableQ)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hKThin : KThinSimple)
    (hE : UC22P20gExcFacts) (hB : ListBNonabelian) (hO : LieOrderFormulasInput)
    (hThin : PartTwo.ThinList13) (hK : PartTwo.S17.K_LieModelNotL2)
    (hGA : GriessAllModelsStatement) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (h207 : S20_7 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h3 : S21_3 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (hR34 : S21_12aFR34 (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S))) :
    S21_12aF (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
  have hσ := UC6S846.sigmaStd_dataOfSetup hS S
  have h15 := s21_15Two_of_certificate113 _ _ h211 hσ (uc22r899e3_dataOfSetup hS hUC S)
  exact s21_12aF_of_s21_12aFR34 hE (uc22p20r_u38_of_griess hGA) hB hO hThin hK hGA h207 h3
    (s21_5_dataOfSetup hSQ hSE hK3 hKThin hS S h82 h15)
    (fun _ _ _ => trivial) hσ (kf7Use_dataOfSetup hSQ hSE hK3 hS S) h82
    (PartTwo.Three.r76Sig_dataOfSetup hSE hK3 hS S) h614
    (F07.r74Card_dataOfSetup hSE hK3 hS hUC hC S) hR34

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22
