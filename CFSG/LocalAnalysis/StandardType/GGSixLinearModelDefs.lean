module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenWire

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSixLinearRankOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
        Nat.card Bs = p ^ (p - 1)

theorem ggSixLinearRankInput_of_tags (hL : GGSixLinearRankOn .PSL)
    (hU : GGSixLinearRankOn .PSU) : GGSixLinearRankInput := by
  intro G _ _ p Bs G₀ t n f ψ hS hlin
  rcases hlin.2.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hL G p Bs G₀ n f ψ hS hlin
  · exact hU G p Bs G₀ n f ψ hS hlin

@[expose] def GGSixLinearTorusModelV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    Nat.card Bs = p ^ (p - 1) →
    (∃ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p ∧
      ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
      (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
        IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
          Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G))) ∧
      ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) →
        z ^ p = 1 → ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs G₀ f z v

theorem ggSixLinearTorusModelV2Input_of_v1 (h : GGSixLinearTorusModelInput) :
    GGSixLinearTorusModelV2Input :=
  fun G _ _ p Bs G₀ t n f ψ hS hlin hcard _ => h G p Bs G₀ t n f ψ hS hlin hcard

@[expose] def GGSixLinearTorusModelV2On (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    Nat.card Bs = p ^ (p - 1) →
    (∃ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p ∧
      ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
      (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
        IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
          Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G))) ∧
      ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) →
        z ^ p = 1 → ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs G₀ f z v

theorem ggSixLinearTorusModelV2Input_of_tags (hL : GGSixLinearTorusModelV2On .PSL)
    (hU : GGSixLinearTorusModelV2On .PSU) : GGSixLinearTorusModelV2Input := by
  intro G _ _ p Bs G₀ t n f ψ hS hlin
  rcases hlin.2.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hL G p Bs G₀ n f ψ hS hlin
  · exact hU G p Bs G₀ n f ψ hS hlin

theorem ggSixLSixTwelveInput_of_kg_v2 (hRk : GGSixLinearRankInput)
    (hTM : GGSixLinearTorusModelV2Input) : GGSixLSixTwelveInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU b hb hCb g hg hgM hlin
  have hS := hctx.fusionSetting hC hU
  have hb1 : b ≠ 1 := ne_one_of_centralizer_le hCb hgM
  have hcard : Nat.card Bs = p ^ (p - 1) :=
    hRk G p Bs _ t n f ψ hS hlin (g⁻¹ * b * g) hg (hS.orderOf_conj hb hb1 g)
      (hS.not_conj_mem hb hCb hgM)
  obtain ⟨hQ, hv⟩ := hTM G p Bs _ t n f ψ hS hlin hcard
    ⟨g⁻¹ * b * g, hg, hS.orderOf_conj hb hb1 g, hS.not_conj_mem hb hCb hgM⟩
  exact ⟨hcard, fun K hK hKA => hS.not_typeAk_of_conj hQ hv hb hCb hg hgM ⟨K, hK, hKA⟩⟩

theorem ggSixStepOneV2Input_of_lemmas_kg_v2 (ha₀ : GGLNoncyclicInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hc₃ : GGNoTransvectionInput) (hnbr : GGSixNbrCentralizerInput)
    (h63 : GGSixCentralizerOddInput) (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (h68i : GGSixInnerOnKdInput) (h69 : GGSixInndiagNormalInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) (h610 : GGSixBstarUniqueV2Input)
    (hKG : GGSixLSixElevenKGInput) (hRk : GGSixLinearRankInput)
    (hTM : GGSixLinearTorusModelV2Input) (h613t : GGSixTrialityInput)
    (h613d : GGSixLinearJInput) : GGSixStepOneV2Input :=
  ggSixStepOneV2Input_of_lemmas ha₀ hc₀ hc₁ hc₂ hc₃ hnbr h63 h64 h65 h66 h68 h68i h69 hS hT h610
    (ggSixLSixElevenInput_of_lemmas hKG ha₀ hnbr h63 h64 h65 h66 h68 h68i h69 hS hT)
    (ggSixLSixTwelveInput_of_kg_v2 hRk hTM) h613t h613d

end Inputs

end CFSG.StandardType
