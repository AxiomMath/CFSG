module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoAutK
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Coprime

variable {G : Type} [Group G]

theorem GGControlsStrongFusionIn.inf_centralizer_le {X H E : Subgroup G}
    (h : GGControlsStrongFusionIn X H E) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    X ⊓ Subgroup.centralizer {e} ≤ H := by
  intro g hg
  obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.mp hg
  refine h.2.2 g hgX fun hbot => he1 ?_
  have hmem : g⁻¹ * e * g ∈ E.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H := by
    refine Subgroup.mem_inf.mpr ⟨⟨e, he, by simp⟩, ?_⟩
    rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hgC, ← mul_assoc, inv_mul_cancel,
      one_mul]
    exact h.1 he
  rw [hbot, Subgroup.mem_bot] at hmem
  calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem ggPPrimeCore_le_of_fusionIn [Finite G] {p : ℕ} (hp : p.Prime) {X H E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (h : GGControlsStrongFusionIn X H E) :
    (CFSG.pPrimeCore p ↥X).map X.subtype ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  have hEX : E ≤ X := h.1.trans h.2.1
  have hcop : ¬ p ∣ Nat.card ((CFSG.pPrimeCore p ↥X).map X.subtype) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact (hp.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
  have hnorm : E ≤ Subgroup.normalizer
      (((CFSG.pPrimeCore p ↥X).map X.subtype : Subgroup G) : Set G) := by
    intro e he
    have hN : (CFSG.pPrimeCore p ↥X).Normal := CFSG.pPrimeCore_normal
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨⟨e, hEX he⟩ * y' * ⟨e, hEX he⟩⁻¹, hN.conj_mem y' hy' _, rfl⟩
    · obtain ⟨z, hz, hzy⟩ := hy
      refine ⟨⟨e, hEX he⟩⁻¹ * z * ⟨e, hEX he⟩, ?_, ?_⟩
      · have := hN.conj_mem z hz (⟨e, hEX he⟩⁻¹)
        simpa using this
      · have hzy' : (z : G) = e * y * e⁻¹ := hzy
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hzy']
        group
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp E _
    (fun e => Subtype.ext (by simpa using hE.2 e e.2)) hEcard hcop hnorm]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he1' : (e : G) ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  exact (inf_le_inf_right _ (Subgroup.map_subtype_le _)).trans
    (h.inf_centralizer_le e.2 he1')

theorem ggIsComponentOf_of_le_pPrimeCore [Finite G] {p : ℕ} (hp : p.Prime) {X H E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (h : GGControlsStrongFusionIn X H E) {L₁ : Subgroup G} (hL : IsComponentOf L₁ H)
    (hLO : L₁ ≤ (CFSG.pPrimeCore p ↥X).map X.subtype) : IsComponentOf L₁ X := by
  have hOH := ggPPrimeCore_le_of_fusionIn hp hE hEcard h
  have hOX : (CFSG.pPrimeCore p ↥X).map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hsn : IsSubnormal L₁ ((CFSG.pPrimeCore p ↥X).map X.subtype) :=
    ggIsSubnormal_of_le_of_le hL.2.1 hLO hOH
  have hN : (((CFSG.pPrimeCore p ↥X).map X.subtype).subgroupOf X).Normal := by
    have : ((CFSG.pPrimeCore p ↥X).map X.subtype).subgroupOf X = CFSG.pPrimeCore p ↥X :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact CFSG.pPrimeCore_normal
  exact ⟨hLO.trans hOX, ggIsSubnormal_trans hsn (ggIsSubnormal_of_normal hOX hN), hL.2.2⟩

end Coprime

@[expose] def GGLemmaThreeFourteenPInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ X H E : Subgroup G,
    (∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K)) →
    IsElemAbelian p E → Nat.card E = p ^ 2 → GGControlsStrongFusionIn X H E →
      ∀ L₁ : Subgroup G, IsComponentOf L₁ H → ¬ L₁ ≤ (CFSG.pPrimeCore p ↥X).map X.subtype →
        ∃ K : Subgroup G, IsComponentOf K X ∧ L₁ ≤ K

theorem ggLemmaThreeFourteenInput_of_p (h : GGLemmaThreeFourteenPInput) :
    GGLemmaThreeFourteenInput := by
  intro G _ _ p hp hp2 X H E hK hE hEcard hfus L₁ hL
  by_cases hLO : L₁ ≤ (CFSG.pPrimeCore p ↥X).map X.subtype
  · exact ⟨L₁, ggIsComponentOf_of_le_pPrimeCore hp hE hEcard hfus hL hLO, le_rfl⟩
  · exact h G p hp hp2 X H E hK hE hEcard hfus L₁ hL hLO

@[expose] def GGLemmaThreeThirteenPInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ X H E : Subgroup G,
    (∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K)) →
    IsElemAbelian p E → Nat.card E = p ^ 2 → GGControlsStrongFusionIn X H E →
      ∀ K : Subgroup G, IsComponentOf K X → ¬ K ≤ (CFSG.pPrimeCore p ↥X).map X.subtype →
        ¬ K ≤ H → E ≤ Subgroup.normalizer (K : Set G)

theorem ggLemmaThreeThirteenInput_of_p (h : GGLemmaThreeThirteenPInput) :
    GGLemmaThreeThirteenInput := by
  intro G _ _ p hp hp2 X H E hK hE hEcard hfus K hKc hKH
  exact h G p hp hp2 X H E hK hE hEcard hfus K hKc
    (fun hKO => hKH (hKO.trans (ggPPrimeCore_le_of_fusionIn hp hE hEcard hfus))) hKH

section Inputs

theorem ggSixStepTwoV2Input_of_coprime (hfus : GGStepTwoBstarFusionInput)
    (hA : GGStepTwoLinearFusionInput) (h313 : GGLemmaThreeThirteenPInput)
    (h314 : GGLemmaThreeFourteenPInput) (hKF : GGKGroupFusionLegacyUnrestrictedInput)
    (hR : GGStepTwoAutKRestInput) (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_autK hfus hA (ggLemmaThreeThirteenInput_of_p h313)
    (ggLemmaThreeFourteenInput_of_p h314) hKF hR h615

theorem ggSixStepTwoV2Input_of_coprime' (h613 : GGStepTwoLemmaSixThirteenInput)
    (hA : GGStepTwoLinearFusionInput) (h313 : GGLemmaThreeThirteenPInput)
    (h314 : GGLemmaThreeFourteenPInput) (hKF : GGKGroupFusionLegacyUnrestrictedInput)
    (hR : GGStepTwoAutKRestInput) (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_inputs h613 hA
    (ggStepTwoSubnormalInput_of_split (ggLemmaThreeFourteenInput_of_p h314)
      (ggStepTwoComponentInput_of_kgroup hKF
        (ggStepTwoAutKInput_of_rest (ggLemmaThreeThirteenInput_of_p h313) hR))) h615

end Inputs

end CFSG.StandardType
