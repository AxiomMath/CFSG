module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

@[expose] def RCKCollinearVia (M : LieUniversal) (β : Fin M.D.rank → ℤ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R V : Subgroup X), GGRootVia M K R β → Nat.card R = 2 →
    ∀ r ∈ R, r ≠ 1 → r ∈ V → V ≤ K → IsElemAbelian 2 V → Nat.card V = 4 →
    (∀ v ∈ V, v ≠ 1 → ∃ k ∈ K, v = k * r * k⁻¹) →
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

@[expose] def RCKCollinearRest :
    Prop :=
  ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F) (g : ℕ)
    (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g →
    GGLongRoot (triD4Universal F σ).D β → RCKCollinearVia (triD4Universal F σ) β

theorem rckK2NbrCollinear_of_via
    (hpos : ∀ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' →
      1 ≤ g → β ∈ (ggU t' m g).D.roots →
      (GGLongRoot (ggU t' m g).D β ∨ (GGShortTag t' ∧ 2 • β ∉ (ggU t' m g).D.roots)) →
      RCKCollinearVia (ggU t' m g) β)
    (htri : ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g →
      GGLongRoot (triD4Universal F σ).D β → RCKCollinearVia (triD4Universal F σ) β) :
    RCKK2NbrCollinear := by
  intro X _ _ K R V hRpos hR2 r hr hr1 hrV hVK hV hV4 hconj
  rcases hRpos with ⟨t', m, g, β, ht, hg, hβ, hcase, hvia⟩ |
    ⟨F, _, _, σ, g, β, hF, hl, hvia⟩
  · exact hpos t' m g β ht hg hβ hcase X K R V hvia hR2 r hr hr1 hrV hVK hV hV4 hconj
  · exact htri F σ g β hF hl X K R V hvia hR2 r hr hr1 hrV hVK hV hV4 hconj

end CFSG.StandardType.RCKC1
