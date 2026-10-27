module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveWeylAt_of_join_eq {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K)
    (hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) :
    GGSecFiveWeylAt p B Bs x L D J M := by
  refine ⟨y, K, hnbr, ?_⟩
  rw [hA]
  exact ⟨e, hP.2⟩

theorem GGSecFiveRouteCfg.exists_join_eq_of_card_le_one {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (h𝒦 : 𝒦.card ≤ 1) :
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  have hMax : GGMaximalJoin p B Bs x L D J 𝒦 := hR.2.2.2
  have hc : 𝒦.card = 0 ∨ 𝒦.card = 1 := by omega
  rcases hc with hc | hc
  · obtain rfl : 𝒦 = ∅ := Finset.card_eq_zero.mp hc
    have hcfg : GGConfig p B Bs x L D J := hR.1.1
    obtain ⟨y, K, hnbr⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
    have hWK : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
      hR.1.2.2.2.2.1 y K hnbr (hR.2.1 y K hnbr) (Or.inr hR.2.1)
    have hWK' : GGWeylReflectionGroup p (ggAutomizerJoin L Bs {K}) := by
      rwa [ggAutomizerJoin_singleton]
    have hle := hMax.2.2 {K} (ggNbrSet_singleton hnbr) hWK'
    rw [ggAutomizerJoin_singleton] at hle
    simp [ggAutomizerJoin] at hle
    have hEq : ggAutomizer L Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
      Subgroup.eq_of_le_of_card_ge le_sup_left hle
    refine ⟨y, K, hnbr, ?_⟩
    rw [← hEq]
    simp [ggAutomizerJoin]
  · obtain ⟨K, rfl⟩ : ∃ K, 𝒦 = {K} := Finset.card_eq_one.mp hc
    obtain ⟨y, hnbr⟩ := hMax.1.2 K (by simp)
    exact ⟨y, K, hnbr, (ggAutomizerJoin_singleton L Bs K).symm⟩

theorem GGSecFiveRouteCfg.weylAt_of_card_le_one {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (h𝒦 : 𝒦.card ≤ 1) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) :
    GGSecFiveWeylAt p B Bs x L D J M := by
  obtain ⟨y, K, hnbr, hA⟩ := hR.exists_join_eq_of_card_le_one h𝒦
  exact ggSecFiveWeylAt_of_join_eq hnbr hA e hP

theorem GGSecFiveWeylAt.of_reindex {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ι ι' : Type} {M : CoxeterMatrix ι} {e : ι ≃ ι'}
    (h : GGSecFiveWeylAt p B Bs x L D J (M.reindex e)) : GGSecFiveWeylAt p B Bs x L D J M := by
  obtain ⟨y, K, hnbr, hW⟩ := h
  exact ⟨y, K, hnbr, hW.of_reindex⟩

theorem GGSecFiveE6QTwoCfg.not_weylAt_E7
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) :
    ¬ GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ := by
  intro hE7
  obtain ⟨𝒦, hcfg, -, ι, M, e, -, ⟨e', hMeq⟩, -⟩ := hC
  have hMax : GGMaximalJoin p B Bs x L D J 𝒦 := hcfg.2.2.2
  have hcardJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 51840 := by
    rw [← Nat.card_congr e.toEquiv]
    rw [hMeq, card_coxeterGroup_reindex, card_coxeterE6_group]
  obtain ⟨y, K, hnbr, hW⟩ := hE7
  have hNbrSet : GGNbrSet p B x D J {K} := ggNbrSet_singleton hnbr
  have hWeylRG : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    GGWeylOfType.weylReflectionGroup ggIsWeylMatrix_E7 hW
  have hWeylRG' : GGWeylReflectionGroup p (ggAutomizerJoin L Bs {K}) := by
    rwa [ggAutomizerJoin_singleton]
  have hle := hMax.2.2 {K} hNbrSet hWeylRG'
  rw [ggAutomizerJoin_singleton, hcardJoin] at hle
  obtain ⟨f, -⟩ := hW
  have hcardA : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 2903040 :=
    (Nat.card_congr f.toEquiv).symm.trans card_coxeterE7_group
  rw [hcardA] at hle
  omega

theorem GGSecFiveE6QTwoCfg.not_weylAt_E8
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) :
    ¬ GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈ := by
  intro hE8
  obtain ⟨𝒦, hcfg, -, ι, M, e, -, ⟨e', hMeq⟩, -⟩ := hC
  have hMax : GGMaximalJoin p B Bs x L D J 𝒦 := hcfg.2.2.2
  have hcardJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 51840 := by
    rw [← Nat.card_congr e.toEquiv]
    rw [hMeq, card_coxeterGroup_reindex, card_coxeterE6_group]
  obtain ⟨y, K, hnbr, hW⟩ := hE8
  have hNbrSet : GGNbrSet p B x D J {K} := ggNbrSet_singleton hnbr
  have hWeylRG : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    GGWeylOfType.weylReflectionGroup ggIsWeylMatrix_E8 hW
  have hWeylRG' : GGWeylReflectionGroup p (ggAutomizerJoin L Bs {K}) := by
    rwa [ggAutomizerJoin_singleton]
  have hle := hMax.2.2 {K} hNbrSet hWeylRG'
  rw [ggAutomizerJoin_singleton, hcardJoin] at hle
  obtain ⟨f, -⟩ := hW
  have hcardA : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 696729600 :=
    (Nat.card_congr f.toEquiv).symm.trans card_coxeterE8_group
  rw [hcardA] at hle
  omega

theorem GGSecFiveE6QTwoCfg.not_innerDiag_and_weylAt
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) :
    ¬ (GGInnerDiagOnLabel GGLabQTwo p Bs L ∧
      (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈)) := by
  intro h
  rcases h.2 with h7 | h8
  · exact hC.not_weylAt_E7 h7
  · exact hC.not_weylAt_E8 h8

theorem ggSecFiveDataResE6QTwoInput_of_e6QTwo
    (h : GGSecFiveWeylE6QTwoInput)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      𝒦.card = 2 → (∀ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs 𝒦) →
      ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e') →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆) :
    GGSecFiveDataResE6QTwoInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 ι M e hP hM hC
  have hE6 : GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ := by
    obtain ⟨𝒦', hR', hnsplit, ι', M', e', hP', ⟨e'', rfl⟩, hdata⟩ := hC
    by_cases hle1 : 𝒦'.card ≤ 1
    · exact (hR'.weylAt_of_card_le_one hle1 e' hP').of_reindex
    · have hc2 : 𝒦'.card = 2 := by
        have := hR'.2.2.2.1.1
        omega
      by_cases hsome : ∃ K ∈ 𝒦', ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦'
      · obtain ⟨K, hK, hA⟩ := hsome
        obtain ⟨y, hnbr⟩ := hR'.2.2.2.1.2 K hK
        exact (ggSecFiveWeylAt_of_join_eq hnbr hA e' hP').of_reindex
      · push Not at hsome
        exact h2 G p B Bs x L D J 𝒦' hR' hc2 hsome hnsplit ι' _ e' hP' ⟨e'', rfl⟩ hdata
  exact h G p B Bs x L D J hR.1 hR.2.1 (Or.inl hE6) hT1 hC.not_innerDiag_and_weylAt hC

end CFSG.StandardType

end
