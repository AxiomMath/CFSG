module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem GGSixFusionSetting.linear_or_triality (hKG : GGSixLSixElevenKGInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hS : GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ)
    (hR : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) {b : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ Subgroup.normalizer (G₀ : Set G)) {g : G}
    (hg : g⁻¹ * b * g ∈ Subgroup.normalizer (G₀ : Set G))
    (hgM : g ∉ Subgroup.normalizer (G₀ : Set G)) :
    GGSixLinearCase p t n f ∨ GGTrialityCaseAt p G₀ (ggU t n f).D t n f ψ (g⁻¹ * b * g) :=
  hKG G p Bs G₀ t n f ψ hS hR b hb (g⁻¹ * b * g) hg
    (hS.orderOf_conj hb (ne_one_of_centralizer_le hC hgM) g) (hS.not_conj_mem hb hC hgM)
    (ggCentralizerEmbeds_conj hC)

theorem ggSixLSixElevenV2Input_of_kg (hKG : GGSixLSixElevenKGInput) :
    GGSixLSixElevenV2Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU h9iii b hb hCb g hg hgM
  exact (hctx.fusionSetting hC hU).linear_or_triality hKG (hctx.twoLocalRankFour h9iii) hb hCb hg
    hgM

theorem ggSixLSixElevenInput_of_kg (hKG : GGSixLSixElevenKGInput)
    (hR : GGSixTwoLocalRankInput) : GGSixLSixElevenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU b hb hCb g hg hgM
  exact (hctx.fusionSetting hC hU).linear_or_triality hKG (hR G p B Bs x L D J t n f ψ hctx hC hU)
    hb hCb hg hgM

theorem GGSixCtxV2.lSixEleven_of_kg (hKG : GGSixLSixElevenKGInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag}
    {n f : ℕ} {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥)
    (hU : GGSixBstarUnique p B Bs x L D J)
    (h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) {b : G} (hb : b ∈ Bs)
    (hCb : Subgroup.centralizer {b} ≤ ggM p B x L D J) {g : G}
    (hg : g⁻¹ * b * g ∈ ggM p B x L D J) (hgM : g ∉ ggM p B x L D J) :
    GGSixLinearCase p t n f ∨
      GGSixTrialityCase p B x L D J (ggU t n f).D t n f ψ (g⁻¹ * b * g) :=
  ggSixLSixElevenV2Input_of_kg hKG G p B Bs x L D J t n f ψ hctx hC hU h9iii b hb hCb g hg hgM

end Inputs

end CFSG.StandardType
