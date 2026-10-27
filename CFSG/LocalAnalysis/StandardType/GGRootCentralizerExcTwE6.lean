module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace RootCentExc

theorem exists_zpowers_sup_of_cyclic {G : Type*} [Group G] {H Y : Subgroup G} {r y₀ : G}
    (hy₀ : y₀ ∈ Y) (hYr : Y ≤ Subgroup.centralizer {r})
    (hk : ∀ y ∈ Y, ∃ k : ℕ, y * (y₀ ^ k)⁻¹ ∈ H)
    (h2 : H ⊓ Subgroup.centralizer {r} ≤ ggOTwoPrime (H ⊓ Subgroup.centralizer {r})) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (H ⊓ Subgroup.centralizer {r}) := by
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  obtain ⟨k, hyk⟩ := hk y hy
  have hmem : y * (y₀ ^ k)⁻¹ ∈ H ⊓ Subgroup.centralizer {r} :=
    ⟨hyk, hYr (Y.mul_mem hy (Y.inv_mem (Y.pow_mem hy₀ k)))⟩
  have e : y = y * (y₀ ^ k)⁻¹ * y₀ ^ k := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup (h2 hmem) (Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) k)

end RootCentExc

section TwE6

@[expose] def GGTwE6RootCentralizerTwoGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* G),
    StatedLieAdmissible .twistedE6 n 2 f →
    ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ r : G, GGRootInvolution (ggU .twistedE6 n f).D .twistedE6 ψ r →
      ψ.range ⊓ Subgroup.centralizer {r} ≤ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r})

@[expose] def GGTwE6InnerDiagCyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* G),
    StatedLieAdmissible .twistedE6 n 2 f →
    ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (ψ.range : Set G) →
      (∀ y ∈ Y, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ y) →
        ∃ y₀ ∈ Y, ∀ y ∈ Y, ∃ k : ℕ, y * (y₀ ^ k)⁻¹ ∈ ψ.range

theorem ggRootCentralizerCyclicTag_twistedE6_of_inputs (h1 : GGTwE6RootCentralizerTwoGenInput)
    (h2 : GGTwE6InnerDiagCyclicInput) : GGRootCentralizerCyclicTag .twistedE6 := by
  intro G _ _ n f ψ hadm _ hker hC r hr Y hY hYd
  obtain ⟨y₀, hy₀, hk⟩ := h2 G n f ψ hadm hker hC Y (fun y hy => (hY hy).1) hYd
  exact RootCentExc.exists_zpowers_sup_of_cyclic hy₀ (fun y hy => (hY hy).2) hk
    (h1 G n f ψ hadm hker hC r hr)

end TwE6

end CFSG.StandardType
