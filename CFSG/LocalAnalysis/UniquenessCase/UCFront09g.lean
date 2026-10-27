module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G]

theorem not_le_of_mem_calMOf (D : Data G) {X N : Subgroup G} (hN : N ∈ calMOf X)
    (hNM : N ≠ D.M) : ¬ N ≤ D.M :=
  fun h => hNM (hN.1.2 D.M D.maxLocal.1 h).symm

theorem calNOf_ne_of_calMOf_ne (D : Data G) {X : Subgroup G} (hXM : X ≤ D.M)
    (hMX : calMOf X ≠ {D.M}) : calNOf X ≠ {D.M} := by
  haveI := D.standing.simple
  obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf X, N ≠ D.M := by
    by_contra h
    push Not at h
    exact hMX (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hXM⟩, h⟩)
  rcases eq_top_or_exists_le_coatom N with h | ⟨N', hN', hNN'⟩
  · exact absurd h (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1)
  · intro hc
    have h' : N' ∈ calNOf X := ⟨hN', hN.2.trans hNN'⟩
    rw [hc] at h'
    exact not_le_of_mem_calMOf D hN hNM (h' ▸ hNN')

theorem mem_calY2_9_of_strong3 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (D : Data G) (hM : IsStronglyPEmbedded 3 D.M)
    {L X : Subgroup G} (hLM : L ≤ D.M) (hLN : D.M ≤ normalizer (L : Set G))
    (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X)
    (hMX : calMOf X ≠ {D.M}) : X ∈ calY2_9 D := by
  haveI := D.standing.simple
  have hXM : X ≤ D.M := hXL.trans hLM
  refine ⟨⟨hXM, calNOf_ne_of_calMOf_ne D hXM hMX, fun A hAX hA3 => ?_⟩, hMX,
    fun N hN => ?_, fun A hA => ?_, ⟨0, ?_⟩⟩
  · exact uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three hM (hAX.trans hXM)
      (IsPGroup.of_card (n := 1) (hA3.trans (pow_one 3).symm)) (by rintro rfl; simp at hA3)
  · by_cases hNM : N = D.M
    · exact Or.inr hNM
    · exact Or.inl (mem_calH9_of_strong3 hG3 hSch D hM hLM hXL hcov hA5 hX
        (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1) hN.2
        (not_le_of_mem_calMOf D hN hNM))
  · rw [hX]
    exact commutator_le_pCoreOf_of_mem_inv9' hLN hXL hcov hA5 hA
  · rw [hX, Subgroup.subgroupOf_self, Subgroup.index_top, pow_zero]

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
