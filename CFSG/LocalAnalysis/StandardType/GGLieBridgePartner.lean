module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartnerInner
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartnerE6
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartnerTwE6

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)

theorem ggLiePartner_exists
    {t : StatedLieTag} {n f : ℕ} (ht : GGExcFive t) (hf : 1 ≤ f)
    {G : Type} [Group G] [Finite G] {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) {θ : ↥G₀ →* ModGL (langTag t) GGL}
    (hrange : θ.range ≤ ggFixGp t f)
    (hθ : ∀ (k : (ggU t n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK t n f hf k)
    {d : G} (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU t n f).D ψ d) :
    ∃ a ∈ ggFixGp t f, GGLiePartner G₀ θ d a := by
  rcases ht with ht | ht | ht | ht | ht
  · exact ggLiePartner_inner (Or.inl ht) hpres hrange hd hψ
  · exact ggLiePartner_E6 ht hf hpres hθ hd hψ
  · exact ggLiePartner_inner (Or.inr (Or.inl ht)) hpres hrange hd hψ
  · exact ggLiePartner_inner (Or.inr (Or.inr ht)) hpres hrange hd hψ
  · exact ggLiePartner_twistedE6 ht hf hpres hθ hd hψ

end CFSG.StandardType.LieCore
