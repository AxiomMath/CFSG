module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Red
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
import CFSG.LocalAnalysis.UniquenessCase.UC22R920OddS217
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VK3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2115NTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS3
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd r920odd_of_r920c)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedSolvable
  StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_17_of_s21_15N_setup4_r920odd
    (hSS : StronglyEmbeddedSolvable)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree)
    (hG : GriessAllModelsStatement) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) {Ch : Choice2011 G}
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h8107 : F08.R8107 (UC6.dataOfSetup4 hS hU S))
    (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S)) (h920 : R920odd (UC6.dataOfSetup4 hS hU S)) :
    S21_15N (UC6.dataOfSetup4 hS hU S) Ch → S21_5 (UC6.dataOfSetup4 hS hU S) Ch →
      S21_12 (UC6.dataOfSetup4 hS hU S) Ch → S21_16 (UC6.dataOfSetup4 hS hU S) Ch →
      (H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch, 3 ≤ c.n) →
      S21_17 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro h15 h5 h212 h16 hn3
  have he : 3 < evenRank G := by have := hS.rank; omega
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have h614 := (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
  have h8100E := r8100E_setup4 hSE hS hU S hMS h614
  have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
        Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  exact s21_17_of_residual _ Ch he h16 (s21_15Two_of_s21_15N hSg.nonempty h15)
    (s21_normalSp4_of _ Ch hSg h211)
    (s21_17R_of_s21_17RPow hG h211 hSg h76
      (s21_17RPow_of_s21_17RV_r920odd hG _ Ch he hK3 (r82_dataOfSetup4 hS hU S hPart.2.2) h8100E h5
        hn3 hSg h76 (UC6.r869NS5_dataOfSetup4_of_inMSigma hSS hSE hK3 hB3 hS hU S hMS) h212 h8107
        h847 h920 hSg.nonempty
        (s21_17RV_of_fourK3 _ Ch h211 h5 hn3 hSg (fun _ hp => UC6.four_le_pRank_of_sigma hp) h614
          (fun p hp _ hsp => h76 p hp hsp) h8107 hK3)))
    h8100E hn3

end CFSG.LocalAnalysis.UniquenessCase.UC22
