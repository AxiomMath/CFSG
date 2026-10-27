module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableKID
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
public import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7)

variable {G : Type} [Group G] [Finite G]

theorem not_alt_of_kIDExcluded (k : Sec7Core4 G) (hno : k.KIDExcluded) (h75 : k.Step75)
    {H : Subgroup G} (hH : k.Config H) {n : ℕ} (hn : 13 ≤ n) :
    IsEmpty (↥(CFSG.generalizedFitting (QuotK7 k.p H)) ≃* alternatingGroup (Fin n)) :=
  ⟨fun e => hno H hH h75 (coverHasLargeTwoLocal_of_mulEquiv_alternatingGroup hn e)⟩

theorem not_isFi22_of_kIDExcluded
    (k : Sec7Core4 G) (hno : k.KIDExcluded) (h75 : k.Step75)
    {H : Subgroup G} (hH : k.Config H) :
    ¬ CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting (QuotK7 k.p H)) := fun hF =>
  hno H hH h75
    (coverHasLargeTwoLocal_of_isFi22 (k.isSimpleGroup_generalizedFitting_quotient hH).1 hF)

theorem kIDExcluded_of_setup4 (hU : CFSG.Open.uniqueFourUnique G)
    (S : CFSG.Yardstones.Mf4cdcdf2e013.Setup4 G) (hMS : S.InMSigma) (hB : BadNoStrongThree)
    (k : Sec7Core4 G) (hkM : k.M = S.M) (hp5 : 5 ≤ k.p) : k.KIDExcluded := by
  by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
  · refine k.kIDExcluded_of_strongThree hp5 ?_ hB
    rw [hkM]
    exact UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hMS h3
  · exact k.kIDExcluded_of_not_mem_beta h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
