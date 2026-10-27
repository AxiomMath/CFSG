module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem theoremCAt_of_r6_3 (D : Data G) (h63 : UC6.R6_3 D) :
    CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt D.M := by
  intro q hq hq2 Q hQM hQq hQrank hΓ H hH hQH
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    CFSG.AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank hq hQrank
  have hEM : E ≤ D.M := hEQ.trans hQM
  have hΓE : rankThreeGamma 1 q E ≤ D.M := by
    unfold rankThreeGamma
    exact (CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono hEQ).trans hΓ
  have hUniq : UniqueMax D.M E := h63 q hq hq2 E hEM hEel hEcard hΓE
  obtain ⟨N, hNmax, hHN⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_le_maxTwoLocal H hH
  have hNmem : N ∈ calMOf E := ⟨hNmax, (hEQ.trans hQH).trans hHN⟩
  have hNM : N = D.M := by
    rw [hUniq] at hNmem
    simpa using hNmem
  calc H ≤ N := hHN
    _ = D.M := hNM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
