module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

theorem ggPsiDiagInner_of_POmegaMinus
    (hm : ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* G)
      (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ →
        ∀ c ∈ Subgroup.normalizer (G₀ : Set G), GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G))
    (t : StatedLieTag)
    (ht : t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E7 ∨ t = .E8) :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU t n f).D t n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU t n f).D ψ c →
          ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ggPsiDiagInner_PSp
  · exact ggPsiDiagInner_POmegaPlus
  · exact hm
  · exact ggPsiDiagInner_F4
  · exact ggPsiDiagInner_E7
  · exact ggPsiDiagInner_E8

end CFSG.StandardType
