module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
import CFSG.LieType.Universal.Symplectic
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutField
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

theorem qTwoLMFrameC_not_psuTrivialMultiplier_four : ¬ PSUTrivialMultiplier 4 := by
  intro h
  have hcard3 : Nat.card (ZMod 3) = 3 := by simp
  have hperf : Group.IsPerfect (StatedSp 2 (ZMod 3)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 (ZMod 3)
      (Or.inr (Or.inl ⟨hcard3, le_rfl⟩))
  have hadm : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hPSp : StatedClassicalModel
      (↥(StatedSp 2 (ZMod 3)) ⧸ Subgroup.center ↥(StatedSp 2 (ZMod 3))) .PSp 2 3 1 :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 (ZMod 3) hadm
      (by simpa using hcard3)
  have hPSU := CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three hPSp
  have hL : LieModel
      (↥(StatedSp 2 (ZMod 3)) ⧸ Subgroup.center ↥(StatedSp 2 (ZMod 3))) .PSU 4 2 1 :=
    Or.inl ⟨by decide, hPSU⟩
  have h1 := h ↥(StatedSp 2 (ZMod 3)) hperf.commutator_eq_top hL
  have h2 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_statedSp_two (k := ZMod 3)
    (by rw [hcard3]; exact ⟨1, rfl⟩)
  omega

end CFSG.StandardType.QTwo

end
