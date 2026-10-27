module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.S23InputsThree
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRestEHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AssemblyUC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S218K
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NoL2SzSectionHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R846Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899E3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

section Certificates

theorem exists_s23Inputs_dataOfSetup_of_rest
    (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h869N : F08.R869N (PartTwo.Three.dataOfSetup hS S))
    (h1930 : H1930 (PartTwo.Three.dataOfSetup hS S))
    (I : S23InputsRest (PartTwo.Three.dataOfSetup hS S)
      (ChoiceZ (PartTwo.Three.dataOfSetup hS S))) :
    ∃ Ch : Choice2011 G, S23Inputs (PartTwo.Three.dataOfSetup hS S) Ch ∧
      S21_8N (PartTwo.Three.dataOfSetup hS S) Ch ∧
        S21_21B (PartTwo.Three.dataOfSetup hS S) Ch := by
  have hSE3 :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB
      RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
        RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        PartOne.Section7.KIB3Small_holds)
  have hK36 : UCK.K36 := UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree
  have h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S) :=
    UC6G.uc_theorem_6_14_three hS hUC hC hK36 S
  let I0 : S23Inputs (PartTwo.Three.dataOfSetup hS S)
      (ChoiceZ (PartTwo.Three.dataOfSetup hS S)) :=
    s23Inputs_dataOfSetup_of_rest hS hUC hC S hMS h82 h869N
      (F10.k105SporRest_of_restB (F10.k105SporRestB_of_restE F10.k105SporRestE_holds)) h1930 I
  refine ⟨ChoiceZ (PartTwo.Three.dataOfSetup hS S), I0, ?_, ?_⟩
  · exact s21_8N_dataOfSetup hSE3 I0.griess PartTwo.S19.k_19_25_noL2SzSection_holds hS hUC hC S
      I0.s21_1 h614 I0.r76Sig I0.r7_2 (s21_8K_dataOfSetup hS S I0.s21_1 h614 I0.r76Sig)
  · exact s21_21B_of_s21_21For I0.s21_21For

theorem tiStage1930_of_rest
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h82 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
          CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
            F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h869N : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
          CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
            F08.R869N (PartTwo.Three.dataOfSetup hS S))
    (hRest : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
          CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
            S23InputsRest (PartTwo.Three.dataOfSetup hS S)
              (ChoiceZ (PartTwo.Three.dataOfSetup hS S))) :
    CFSG.Yardstones.Me2c15c2c995a.AscSectionTwentyThree := by
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hK36 : UCK.K36 := UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree
  exact tiStage1930_of_s23InputsUC uc22p20g_excFacts
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hC
    (fun G _ _ hS hUC hc S _ => PartTwo.Three.r846_dataOfSetup global22yNo_holds.griess
      PartOne.Section7.SEFive.stronglyEmbeddedFive_holds hSE3 hS hUC hc hK36 S)
    (fun G _ _ hS hUC S _ _ _ => uc22r899e3_dataOfSetup hS hUC S)
    (fun G _ _ hS hUC hc S hMS h1930 hTI =>
      exists_s23Inputs_dataOfSetup_of_rest hS hUC hc S hMS
        (h82 G hS hUC hc S hMS h1930 hTI)
        (h869N G hS hUC hc S hMS h1930 hTI)
        (by simpa [H1930, PartTwo.Three.dataOfSetup] using h1930)
        (hRest G hS hUC hc S hMS h1930 hTI))

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UC22
