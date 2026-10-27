module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Labels

@[expose] def GGSixBstarNoOffenderOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGNoOffender p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderAt_of_on {P Q : StatedLieTag → ℕ → ℕ → ℕ → Prop} (t : StatedLieTag)
    (hP : GGSixBstarNoOffenderOn P) (hQ : GGSixBstarNoOffenderOn Q)
    (hPQ : ∀ n f p, P t n f p ∨ Q t n f p) : GGSixBstarNoOffenderAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx hC
  rcases hPQ n f p with h | h
  · exact hP G p B Bs x L D J t n f ψ h hctx hC
  · exact hQ G p B Bs x L D J t n f ψ h hctx hC

@[expose] def GGPSLSplitCoprime (t : StatedLieTag) (n f p : ℕ) : Prop :=
  t = .PSL ∧ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ n

@[expose] def GGPSLSplitDvd (t : StatedLieTag) (n f p : ℕ) : Prop :=
  t = .PSL ∧ p ∣ 2 ^ f - 1 ∧ p ∣ n

theorem ggSixBstarNoOffenderOn_PSLSplit_of_on (h₁ : GGSixBstarNoOffenderOn GGPSLSplitCoprime)
    (h₂ : GGSixBstarNoOffenderOn GGPSLSplitDvd) : GGSixBstarNoOffenderOn GGPSLSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  by_cases hpn : p ∣ n
  · exact h₂ G p B Bs x L D J t n f ψ ⟨hP.1, hP.2, hpn⟩ hctx hC
  · exact h₁ G p B Bs x L D J t n f ψ ⟨hP.1, hP.2, hpn⟩ hctx hC

theorem ggSixBstarNoOffenderAt_PSp_of_on (h₁ : GGSixBstarNoOffenderOn GGPSpSplit)
    (h₂ : GGSixBstarNoOffenderOn GGPSpNonsplit) : GGSixBstarNoOffenderAt .PSp :=
  ggSixBstarNoOffenderAt_of_on .PSp h₁ h₂ fun _ f p => by
    by_cases hp : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨rfl, hp⟩
    · exact Or.inr ⟨rfl, hp⟩

theorem ggSixBstarNoOffenderAt_PSL_of_on (h₁ : GGSixBstarNoOffenderOn GGPSLSplit)
    (h₂ : GGSixBstarNoOffenderOn GGPSLNonsplit) : GGSixBstarNoOffenderAt .PSL :=
  ggSixBstarNoOffenderAt_of_on .PSL h₁ h₂ fun _ f p => by
    by_cases hp : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨rfl, hp⟩
    · exact Or.inr ⟨rfl, hp⟩

end Labels

end CFSG.StandardType
