module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Fusion

variable {G : Type} [Group G]

theorem ggStepTwo_isSubnormal_sup_zpowers {L₁ : Subgroup G} {b : G}
    (hsn : IsSubnormal L₁ (Subgroup.centralizer {b})) :
    IsSubnormal (Subgroup.zpowers b ⊔ L₁) (Subgroup.centralizer {b}) := by
  have hbC : b ∈ Subgroup.centralizer (Subgroup.centralizer {b} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg
  have hsn' := ggIsSubnormal_sup_zpowers hsn hbC
  have htop : Subgroup.zpowers b ⊔ Subgroup.centralizer {b} = Subgroup.centralizer {b} :=
    sup_eq_right.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  rwa [htop] at hsn'

theorem ggStepTwo_centralizer_le_of_conj_mem {M D L₁ : Subgroup G} {b a m : G}
    (hD : GGControlsStrongFusion M D) (hbM : b ∈ M) (hL₁M : L₁ ≤ M)
    (hsn : IsSubnormal L₁ (Subgroup.centralizer {b})) (haR : a ∈ Subgroup.zpowers b ⊔ L₁)
    (ha1 : a ≠ 1) (hm : m ∈ M) (hmD : m⁻¹ * a * m ∈ D) :
    Subgroup.centralizer {b} ≤ M := by
  have hfus : GGControlsStrongFusion M (Subgroup.zpowers a) := by
    refine hD.of_map_conj_le hm ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hmD
  exact hfus.le_of_isSubnormal (Subgroup.mem_zpowers a) ha1 haR
    (sup_le (Subgroup.zpowers_le.mpr hbM) hL₁M) (ggStepTwo_isSubnormal_sup_zpowers hsn)

end Fusion

section Inputs

@[expose] def GGStepTwoFusedWitnessInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          ∃ a ∈ Subgroup.zpowers b ⊔ L₁, a ≠ 1 ∧ ∃ m ∈ ggM p B x L D J, m⁻¹ * a * m ∈ D

@[expose] def GGStepTwoToralWitnessInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D

theorem ggStepTwoFusedWitnessInput_of_toral (h : GGStepTwoToralWitnessInput) :
    GGStepTwoFusedWitnessInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair _ _
  obtain ⟨a, ha, ha1, m, hm, hmD⟩ := h G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
  exact ⟨a, (Subgroup.mem_inf.mp ha).2, ha1, m,
    Subgroup.le_normalizer (Subgroup.mem_inf.mp hm).1, hmD⟩

theorem ggStepTwoCentralizerInput_of_fusedWitness (h : GGStepTwoFusedWitnessInput) :
    GGStepTwoCentralizerInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
  obtain ⟨-, -, -, -, -, ⟨hBsM, -⟩, -, -⟩ := hctx.2
  obtain ⟨a, haR, ha1, m, hm, hmD⟩ :=
    h G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
  exact ggStepTwo_centralizer_le_of_conj_mem s1.2.1 (hBsM hpair.1) hpair.le_ggM hsn haR ha1 hm hmD

theorem ggStepTwoContraryXInput_of_fusedWitness (h : GGStepTwoFusedWitnessInput) :
    GGStepTwoContraryXInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR _
  exact inf_le_left.trans (ggStepTwoCentralizerInput_of_fusedWitness h G p B Bs x L D J t n f ψ
    hctx s1 hlin b L₁ hpair hsn hDR)

theorem ggStepTwoContraryNormalizerInput_of_fusedWitness (h : GGStepTwoFusedWitnessInput) :
    GGStepTwoContraryNormalizerInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR _
  exact ggStepTwoCentralizerInput_of_fusedWitness h G p B Bs x L D J t n f ψ hctx s1 hlin b L₁
    hpair hsn hDR

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepTwoV2Input_of_fused (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hKF : GGKGroupFusionLayerInput) (hRat : GGSixAutKHypRestAtInput)
    (h5 : GGStepTwoAutKFiveInput) (h3 : GGStepTwoAutKThreeInput)
    (hfw : GGStepTwoFusedWitnessInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_schreierLayer hSch h613 hA hKF (ggStepTwoAutKRestInput_of_finer hRat h5 h3)
    (ggStepTwoCentralizerInput_of_fusedWitness hfw)

end Inputs

end CFSG.StandardType
