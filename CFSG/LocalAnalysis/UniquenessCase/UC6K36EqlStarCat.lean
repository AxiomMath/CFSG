module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Ge4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Cat
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36CatSpor
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporFinal
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltStar
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporFalse

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (Star36)
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)

@[expose] def K36EqlStarSporGe4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 3 < twoLocalPrimeRank q G) →
      ∀ (M : Subgroup G) (p : ℕ) (E : Subgroup G), Hyp36 G M p E → Star36 G →
        ∀ L : Subgroup G, L.Normal → CFSG.IsComponent L → ⁅L, pCoreOf 2 M⁆ ≠ ⊥ →
          E ⊔ pCoreOf 2 M ⊔ L = ⊤ → ∀ s : TauCeti.SporadicName, s ∉ sporadicsThm3 →
            Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → K36Concl M p

section Spor


theorem Hyp36.false_of_sporadic_thm3 {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}
    (hK : K315Spor) (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {s : TauCeti.SporadicName} (hs : s ∈ sporadicsThm3)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  obtain ⟨Ē, R, hconf⟩ := h.exists_sporPlaneConf hL hne φ
  exact h.false_of_spor hL hne (hK s hs p h.prime h.odd Ē R hconf) φ

end Spor

section Parts


theorem k36EqlStar_of_catalog (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (hR : K36OddDefChar) (hK315 : K315Spor)
    (hGe4 : K36EqlStarSporGe4) : K36EqlStar := by
  intro G _ _ hK M p E h hSt L hL hLc hne hX
  haveI := hL
  have hLM : L ⊔ M = ⊤ := by
    refine top_le_iff.1 (hX.symm.le.trans ?_)
    exact sup_le (sup_le (h.E_le.trans le_sup_right) ((CFSG.openPCoreOf_le 2 M).trans le_sup_right))
      le_sup_left
  refine h.concl_of_catalog hS hR hLc hne hLM (isCatalogGroup_quotient_center_of_component hK hLc) ?_ ?_
  · rintro n hn ⟨φ⟩
    exact h.k36Concl_of_alt_of_star hLc hne hLM φ hn hSt
  · rintro s ⟨φ⟩
    by_cases hs : s ∈ sporadicsThm3
    · exact (h.false_of_sporadic_thm3 hK315 hLc hne hs φ).elim
    · by_cases he : ∀ q : ℕ, q.Prime → q ≠ 2 → twoLocalPrimeRank q G ≤ 3
      · exact (hs (mem_sporadicsThm3_of_component he hLc φ)).elim
      · push Not at he
        exact hGe4 G hK he M p E h hSt L hL hLc hne hX s hs ⟨φ⟩

end Parts

end CFSG.LocalAnalysis.UniquenessCase.UCK
