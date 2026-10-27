module

public import CFSG.LocalAnalysis.StandardType.GGHypSixAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGInnerDiagMpInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → ∀ G₀ : Subgroup G, ψ.range = G₀ →
    ∀ P : LargeEvenMarkProp ↥G₀, LargeEvenMarking ↥G₀ P →
      LargeEvenMarking ↥G₀ (fun lab R _ I F θ => P lab R I F θ ∧
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
          (∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) →
            GGPsiInnerDiag (ggU t n f).D ψ c)

theorem ggInnerDiagMpInput_of_bridge (hR : GGInnerDiagBridgeInput) : GGInnerDiagMpInput := by
  intro G _ _ t n f ψ hadm hrk hker G₀ hrange P hP
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, fun c hc hI => (h.2 c hc).mp hI⟩)
    (hR G t n f ψ hadm hrk hker G₀ hrange P hP)

variable {G : Type} [Group G] [Finite G]

theorem ggTorusOnRoot_of_innerDiagOn_mp (hMp : GGInnerDiagMpInput) {U : Type*} [Group U]
    {Δ : UniversalRootDatum U} {ψ : U →* G} {Bs K : Subgroup G} (hK : GGInnerDiagOn Bs K)
    (hcomp : GGCompatPresented Δ ψ K) (hKle : K ≤ ψ.range) :
    ∃ γ ∈ Δ.roots, ∃ u : U, ∀ b ∈ Bs, GGTorusOnRoot Δ ψ b γ u := by
  obtain ⟨t', n', f', ψ', hadm', hrk', hker', hrange', δ, hδ, γ, hγ, u, hm⟩ := hcomp
  obtain ⟨-, lab, -, hraw⟩ := hMp G t' n' f' ψ' hadm' hrk' hker' K hrange' _ hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  refine ⟨γ, hγ, u, fun b hb => ?_⟩
  exact ggTorusOnRoot_of_rootMatch (hrange' ▸ hKle) hδ hm (himp b (hBsN hb) (hI b hb))

theorem ggHypSixV2Input_of_detect_mp (hMp : GGInnerDiagMpInput) (hC : GGCompatNbrInput)
    (hdet : ∀ t, GGRootDetect t) (hD4 : GGHypSixD4Input) : GGHypSixV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN b hb
  by_cases hD : t = .POmegaPlus ∧ n = 4 ∧ p = 3
  · obtain ⟨rfl, rfl, rfl⟩ := hD
    exact hD4 G B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb
  have hp : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  obtain ⟨K, hK, hcomp⟩ := hC G p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  have hKinn : GGInnerDiagOn Bs K := by
    rcases hK with rfl | ⟨y, hy⟩
    · exact hInn.1
    · exact hInn.2 y K hy
  have hKle : K ≤ ψ.range := by
    rw [hpres.2.1.1]
    rcases hK with rfl | ⟨y, hy⟩
    · exact le_ggG0_left p B x K D J
    · exact le_ggG0_of_ggNbr hy
  have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hpres.2.1.1]
    exact hBsN hb
  have hbp : b ^ p ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hcfg.2.1.2.1.2 b hb]
    exact Subgroup.one_mem _
  obtain ⟨γ, hγ, u, hall⟩ := ggTorusOnRoot_of_innerDiagOn_mp hMp hKinn hcomp hKle
  exact hdet t G n f ψ hpres.1.1 hpres.1.2 hpres.2.1.2 p hp.1 hp.2.1 hD b hbN hbp γ hγ u
    (hall b hb)

theorem ggHypSixV2Input_of_rest_mp (hMp : GGInnerDiagMpInput) (hC : GGCompatNbrInput)
    (hrest : GGRootDetectRest) (hD4 : GGHypSixD4Input) : GGHypSixV2Input :=
  ggHypSixV2Input_of_detect_mp hMp hC (ggRootDetect_all hrest) hD4

end CFSG.StandardType
