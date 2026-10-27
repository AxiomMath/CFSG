module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925L2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925J1
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def OddIdxPropL3U3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ),
    (p ^ f % 3 = 2 ∧ LieModel K .PSL 3 p f ∨ p ^ f % 3 = 1 ∧ LieModel K .PSU 3 p f) →
      OddIdxProp K

theorem oddIdxAll_of_oddIdxProp
    (h : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsKGroup K → IsSimpleGroup K →
      (∃ a b : K, a * b ≠ b * a) → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 → OddIdxProp K) :
    OddIdxAll := by
  intro Λ _ _ K N Y D hKG hKs hKn hr hNK hNne hNodd hD hDY hYN hnorm hY hcat
  have hDK : D ≤ K := hDY.trans (hYN.trans hNK)
  have hYK : Y ≤ K := hYN.trans hNK
  have hres := h ↥K hKG hKs hKn
    (by rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]; exact hr)
    (N.subgroupOf K) (Y.subgroupOf K) (D.subgroupOf K)
    (by
      intro htop
      exact hNne (le_antisymm hNK (Subgroup.subgroupOf_eq_top.mp htop)))
    hNodd
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]; exact hD)
    (Subgroup.subgroupOf_mono K hDY)
    (Subgroup.subgroupOf_mono K hYN)
    (by
      rw [← Subgroup.subgroupOf_normalizer_eq hDK,
        ← Subgroup.inf_subgroupOf_left (normalizer D) K]
      exact Subgroup.subgroupOf_mono K hnorm)
    (hY.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYK).symm)
    (CFSG.KCore.KGroupNonab.of_mulEquiv (isoInvariant_dvdOrThreeFree 51840) hcat
      (Subgroup.subgroupOfEquivOfLe hNK))
  refine ⟨hres.1, ?_⟩
  obtain ⟨F, hF, hFf, hc, ⟨e⟩⟩ := hres.2
  exact ⟨F, hF, hFf, hc, ⟨(Subgroup.subgroupOfEquivOfLe hYK).symm.trans e⟩⟩

theorem oddIdxProp_of_k32
    (hK32 : UCK.K32) (hL3U3 : OddIdxPropL3U3) (K : Type)
    [Group K] [Finite K] (hKG : CFSG.Open.IsKGroup K) (hs : IsSimpleGroup K)
    (hn : ∃ a b : K, a * b ≠ b * a)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1) : OddIdxProp K := by
  rcases hK32 K hKG hs hn hr with ⟨p, f, h⟩ | ⟨p, f, h3, h⟩ | ⟨p, f, h3, h⟩ | h
  · by_cases hp : p = 3
    · subst hp
      exact absurd hr (by have := two_le_pRank_psl2_three_pow h; omega)
    · exact oddIdxProp_psl2 hp h
  · exact hL3U3 K p f (Or.inl ⟨h3, h⟩)
  · exact hL3U3 K p f (Or.inr ⟨h3, h⟩)
  · exact oddIdxProp_j1 h

theorem oddIdxAll_of_k32
    (hK32 : UCK.K32) (hL3U3 : OddIdxPropL3U3) : OddIdxAll :=
  oddIdxAll_of_oddIdxProp fun K _ _ hKG hs hn hr => oddIdxProp_of_k32 hK32 hL3U3 K hKG hs hn hr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
