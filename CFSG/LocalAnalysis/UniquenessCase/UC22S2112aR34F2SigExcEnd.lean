module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Setup4S21Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2SigReduction
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2SigExcCore
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem s21_12aFR34F2SigExc_core {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34F2SigExc (UC6.dataOfSetup4 hS hU S)
      (Choice214U (UC6.dataOfSetup4 hS hU S)) := by
  have hs := setup4S21PreRestFacts_dataOfSetup4 hS hU S hMS hPart
  intro hH c L hL p hp hp2 _hpσ hp7 hX hno hfaith
  have hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → True :=
    fun _ _ _ => trivial
  have hBN : c.B0 ≤ normalizer (L : Set G) :=
    uc22s2114_B0_le_normalizer hs.s21_5 hH (c.mono hCh) hL
  exact uc22s2112r34_false_exc CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hH c (hs.hn3 hH (c.mono hCh)) hL hBN hfaith hp hp2
    hp7 hX hno

end CFSG.LocalAnalysis.UniquenessCase.UC22
