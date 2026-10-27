module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3X
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs)

variable {G : Type} [Group G] [Finite G]

theorem s21_8XE3_setup4
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_8XE3 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL n hn p hp hcase
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
        Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  exact uc22s218n_pRank_le_three_U5_exc hGA _ Ch (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) h211 h76 hH c hL hcase.1 hn hp hcase.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
