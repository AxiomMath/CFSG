module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G]

@[expose] def GGSixSeventeenExcluded (p : ℕ) (t : StatedLieTag) (f : ℕ) (L₁ : Subgroup G) :
    Prop :=
  (p = 3 ∧ (LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 4 2 1 ∨
      Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* alternatingGroup (Fin 6)) ∨
      LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1)) ∨
    (p = 5 ∧ (LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 2 ∨
      LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1)) ∨
    (t = .PSL ∧ p ∣ 2 ^ f - 1 ∧ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f) ∨
    (t = .PSU ∧ p ∣ 2 ^ f + 1 ∧ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f) ∨
    ∃ k : ℕ, LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL k 2 (2 * f)

@[expose] def GGSixFusionWitness (p : ℕ) (Bs D E G₀ : Subgroup G) (t : StatedLieTag) (f : ℕ)
    (b : G) : Prop :=
  b ≠ 1 ∧ (b ∈ D ∨ b ∈ E ∨ (b ∈ Bs ∧ ∃ L₁ : Subgroup G,
    IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) ∧
      (Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 ∨
        ¬ GGSixSeventeenExcluded p t f L₁)))

@[expose] def GGRootFusionWitnessAlt (p : ℕ) (Bs D E G₀ M : Subgroup G) (t : StatedLieTag)
    (f : ℕ) (r s : G) : Prop :=
  (∃ m ∈ M, s = m⁻¹ * r * m) ∨
    (∃ y : G, y * s = s * y ∧ ∃ m ∈ M, GGSixFusionWitness p Bs D E G₀ t f (m * y * m⁻¹)) ∨
    ¬ ∃ φ : ↥(ggCentOTwoPrime G₀ s) →* ↥(ggCentOTwoPrime G₀ r), Function.Injective φ

@[expose] def GGLinearUnitaryTag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU

@[expose] def GGOtherClassicalTag (t : StatedLieTag) : Prop :=
  t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus

@[expose] def GGExceptionalTag (t : StatedLieTag) : Prop :=
  ¬ GGLinearUnitaryTag t ∧ ¬ GGOtherClassicalTag t

end Defs

theorem ggRootFusionAlt_of_conj_controls {G : Type*} [Group G] {G₀ M : Subgroup G} {r s y m : G}
    (hys : y * s = s * y) (hm : m ∈ M) (hb1 : m * y * m⁻¹ ≠ 1)
    (hfus : GGControlsStrongFusion M (Subgroup.zpowers (m * y * m⁻¹))) :
    GGRootFusionAlt G₀ M r s := by
  have hy : m⁻¹ * (m * y * m⁻¹) * m = y := by group
  refine Or.inr (Or.inl ⟨y, fun h => hb1 (by rw [h]; group), hys, ?_⟩)
  have := ggControlsStrongFusion_zpowers_conj hfus hm
  rwa [hy] at this

theorem ggRootFusionAlt_of_witnessAlt {G : Type} [Group G] {p : ℕ} {Bs D E G₀ M : Subgroup G}
    {t : StatedLieTag} {f : ℕ} {r s : G}
    (hW : ∀ b : G, GGSixFusionWitness p Bs D E G₀ t f b →
      GGControlsStrongFusion M (Subgroup.zpowers b))
    (h : GGRootFusionWitnessAlt p Bs D E G₀ M t f r s) : GGRootFusionAlt G₀ M r s := by
  rcases h with hconj | ⟨y, hys, m, hm, hwit⟩ | hα
  · exact Or.inl hconj
  · exact ggRootFusionAlt_of_conj_controls hys hm hwit.1 (hW _ hwit)
  · exact Or.inr (Or.inr hα)

section Inputs

@[expose] def GGSixLemmaSixSeventeenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        ¬ GGSixSeventeenExcluded p t f L₁ →
          GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b)

@[expose] def GGSixRootFusionWitnessInputFor (P : StatedLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ s ∈ ggG0 p B x L D J, orderOf s = 2 →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) t f r s

@[expose] def GGSixRootFusionWitnessInput : Prop :=
  GGSixRootFusionWitnessInputFor fun _ => True

theorem ggSixRootFusionWitnessInput_of_families
    (hlin : GGSixRootFusionWitnessInputFor GGLinearUnitaryTag)
    (hcl : GGSixRootFusionWitnessInputFor GGOtherClassicalTag)
    (hex : GGSixRootFusionWitnessInputFor GGExceptionalTag) : GGSixRootFusionWitnessInput := by
  intro G _ _ p B Bs x L D J t n f ψ _
  by_cases h₁ : GGLinearUnitaryTag t
  · exact hlin G p B Bs x L D J t n f ψ h₁
  by_cases h₂ : GGOtherClassicalTag t
  · exact hcl G p B Bs x L D J t n f ψ h₂
  exact hex G p B Bs x L D J t n f ψ ⟨h₁, h₂⟩

theorem ggSixFusionWitness_controls (h17 : GGSixLemmaSixSeventeenInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag}
    {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    (s2 : GGSixStepTwo p B Bs x L D J) {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) {b : G}
    (hb : GGSixFusionWitness p Bs D E (ggG0 p B x L D J) t f b) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
  obtain ⟨hb1, hbD | hbE | ⟨hbBs, L₁, hL₁, hcard | hnex⟩⟩ := hb
  · exact s1.2.1.mono_of_le_fusion (Subgroup.zpowers_le.mpr hbD)
  · exact hch.2.2.2.1.mono_of_le_fusion (Subgroup.zpowers_le.mpr hbE)
  · exact (s2 b hbBs hb1 L₁ hL₁ hcard).2
  · exact h17 G p B Bs x L D J t n f ψ hctx s1 s2 b hbBs hb1 L₁ hL₁ hnex

theorem ggSixRootFusionCaseInput_of_witness (hW : GGSixRootFusionWitnessInput)
    (h17 : GGSixLemmaSixSeventeenInput) : GGSixRootFusionCaseInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd s hs hs2
  exact ggRootFusionAlt_of_witnessAlt
    (fun _ hb => ggSixFusionWitness_controls h17 hctx s1 s2 hch hb)
    (hW G p B Bs x L D J t n f ψ trivial hctx s1 s2 E r hch hC hodd s hs hs2)

theorem ggSixStepThreeDInput_of_witness (hW : GGSixRootFusionWitnessInput)
    (h17 : GGSixLemmaSixSeventeenInput) : GGSixStepThreeDInput :=
  ggSixStepThreeDInput_of_caseInput (ggSixRootFusionCaseInput_of_witness hW h17)

end Inputs

end CFSG.StandardType
