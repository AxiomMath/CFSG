module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62GammaAll
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inU_of_uniqueMax {M E : Subgroup G} (hmax : rankThreeIsMaxTwoLocal M)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax M E) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU M E := by
  have hmem : M ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := by
    have h1 : M ∈ ({M} : Set (Subgroup G)) := Set.mem_singleton M
    rwa [← h] at h1
  have hEM : E ≤ M := (Set.mem_setOf.mp hmem).2
  refine ⟨hEM, ?_⟩
  intro g hEconj
  have hmaxg : rankThreeIsMaxTwoLocal (CFSG.Open.uniqueFourConj g M) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hmax (MulAut.conj g⁻¹)
  have hmemg : CFSG.Open.uniqueFourConj g M ∈
      CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hmaxg, hEconj⟩
  rw [h] at hmemg
  exact Set.mem_singleton_iff.mp hmemg

theorem inU_of_isElemAbelian_card_nine_le_of_isSylowOf
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D)
    {L Q E : Subgroup G} (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hΓ : rankThreeGamma 1 3 Q ≤ D.M)
    (hE : E ≤ L) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    CFSG.LocalAnalysis.UniquenessCase.UC6.InU D.M E :=
  inU_of_uniqueMax D.maxLocal
    (uniqueMax_of_isElemAbelian_card_nine_le_of_isSylowOf h63 hLM hQ hΓ hE hEel hEcard)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
