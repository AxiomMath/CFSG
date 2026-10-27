module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Setup4S21Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Cases
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Rank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Section
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem s21_12aFR34F2Even2_dataOfSetup4_of_exc {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34F2Even2 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) := by
  have hF := setup4S21PreRestFacts_dataOfSetup4 hS hU S hMS hPart
  exact s21_12aFR34F2Even2_of_exc kFunSplit_holds
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hF.kf7 hF.hn3 hF.s21_5 hF.r82 hF.s21_1
    (fun _ _ _ => trivial) uc22ExcTwoFun_g2 uc22ExcTwoFunWeak_trialityD4
    triD4OuterThreeRank_holds triD4OuterThreeSection_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
