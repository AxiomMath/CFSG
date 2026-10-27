module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddMain
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseFour
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem r920odd_dataOfSetup4_of_branches (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hSQ : StronglyEmbeddedSolvableQ) (hK : UCK.K332Cyc)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M)
    (hgt : ∀ (L D₃ Y H : Subgroup G) (q : ℕ), Slice (UC6.dataOfSetup4 hS hU S) L D₃ Y H q → 7 < q →
      ∀ E : Subgroup G, F09.Hyp91 (UC6.dataOfSetup4 hS hU S) Y H E →
      (∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M) → False)
    (heq : ∀ (L D₃ Y H : Subgroup G) (q : ℕ), Slice (UC6.dataOfSetup4 hS hU S) L D₃ Y H q → q = 7 →
      ∀ E : Subgroup G, F09.Hyp91 (UC6.dataOfSetup4 hS hU S) Y H E →
      (∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M) → False) :
    R920odd (UC6.dataOfSetup4 hS hU S) := by
  have hC76 := Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
    by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  exact r920odd_of_inputs _ hK3 hK (r82_dataOfSetup4 hS hU S hPart.2.2)
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)
    h76 (kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS) hgt heq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
