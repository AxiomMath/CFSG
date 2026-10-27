module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E4
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
import CFSG.LocalAnalysis.UniquenessCase.UC6K47d
import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive C76Three)

variable {G : Type} [Group G] [Finite G]

theorem r77E2_of_conclusion76 (D : UC22.Data G)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) :
    UC22.F07.R77E2 D := by
  intro _ p hp _ hsp r hr _ hrσ E hEM hEel hEcard h2
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  exact UC6R77.rankThreeGamma_le_of_two_lt_pRank hpr (h76 p hp hsp) hEM hEel hEcard h2

theorem r77E4_of_conclusion76 (D : UC22.Data G)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h69 : R6_9 D)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig → CFSG.Open.pRank r D.M ≤ 3) :
    UC22.F07.R77E4 D := by
  intro hsub p hp _ hsp r hr hr2 hrσ X hXM hX hnc hexp hcl h3
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  exact UC6R77.rankThreeGamma_le_of_three_lt_pRank hr2 hpr hsp (h76 p hp hsp)
    (sixNineAt_of_R6_9 h69 hsub hr hr2 hXM hX hexp hcl)
    ((CFSG.SectionRank.pRank_mono hr.one_lt hXM).trans (hrk r hr hr2 hrσ)) hXM hX hnc hexp hcl h3

theorem r77Use_of_conclusion76 (D : UC22.Data G)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h69 : R6_9 D)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig → CFSG.Open.pRank r D.M ≤ 3) :
    UC22.F07.R77Use D :=
  ⟨r77E2_of_conclusion76 D h76, r77E4_of_conclusion76 D h76 h69 hrk⟩

theorem r77Use_dataOfSetup4_of_mem_uniqueFourBeta (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (h3 : 3 ∈ uniqueFourBeta G) (hC76 : C76Three S)
    (h69 : R6_9 (dataOfSetup4 hS hU S)) : UC22.F07.R77Use (dataOfSetup4 hS hU S) :=
  r77Use_of_conclusion76 _ (fun p hp hsp => hC76 hMS h3 p hp hsp) h69
    fun _ hr hr2 hrσ => pRank_le_three_of_not_mem_sigma hU S.maxLocal hr hr2 hrσ

theorem r77Use_dataOfSetup4_of_K36_of_C76Three (hSE : StronglyEmbeddedFive) (hK36 : UCK.K36)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hC : TheoremCAt S.M) (hC76 : C76Three S) : UC22.F07.R77Use (dataOfSetup4 hS hU S) := by
  by_cases h3 : 3 ∈ uniqueFourBeta G
  · exact r77Use_dataOfSetup4_of_mem_uniqueFourBeta hS hU S hMS h3 hC76
      (r6_9_of_K47 hS hU S k47_uc6 hC
        (PartTwo.r6_7_of_K36_at (dataOfSetup4 hS hU S) hK36 (r6_3_dataOfSetup4 hS hU S hC)
          (star36_holds G hS hU S hMS hC)))
  · exact r77Use_dataOfSetup4_of_K36 hSE hK36 hS hU S hMS hC h3

end CFSG.LocalAnalysis.UniquenessCase.UC6
