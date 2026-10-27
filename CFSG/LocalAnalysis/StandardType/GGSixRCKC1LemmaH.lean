module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHA
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHBC
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHD
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHE67
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHOmM
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHAdj
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTriD4

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.Open
  CFSG.ComponentClassification.RankTwoOddLie

theorem rck_lemmaHC_tw
    {t' : StatedLieTag} (ht : t' = .PSU ∨ t' = .POmegaMinus ∨ t' = .twistedE6) {m g : ℕ}
    (hg : 1 ≤ g) {β : Fin (ggU t' m g).D.rank → ℤ} (hβ : GGLongRoot (ggU t' m g).D β) :
    RCKLemmaHCent (ggU t' m g) β := by
  rcases ht with rfl | rfl | rfl
  · exact rck_lemmaHC_PSU hg hβ
  · exact rck_lemmaHC_POmegaMinus hg hβ
  · exact rck_lemmaHC_twistedE6 hg hβ

@[expose] def RCKLemmaHLong :
    Prop :=
  (∀ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' → 1 ≤ g →
      GGLongRoot (ggU t' m g).D β → RCKLemmaHCent (ggU t' m g) β) ∧
    ∀ (F : Type) [Field F] [Finite F] (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g →
        GGLongRoot (triD4Universal F σ).D β → RCKLemmaHCent (triD4Universal F σ) β

theorem rck_lemmaH_long :
    RCKLemmaHLong := by
  constructor
  · intro t' m g β ht hg hβ
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rck_lemmaHC_A hg hβ
    · exact rck_lemmaHC_tw (Or.inl rfl) hg hβ
    · exact rck_lemmaHC_BC hg hβ
    · exact rck_lemmaHC_D hg hβ
    · exact rck_lemmaHC_tw (Or.inr (Or.inl rfl)) hg hβ
    · exact rck_lemmaH_of_parts (rck_lemmaH_F4 hg hβ).1 (rck_lemmaH_F4 hg hβ).2
    · exact rck_lemmaHC_E67 (Or.inl rfl) hg hβ
    · exact rck_lemmaHC_E67 (Or.inr rfl) hg hβ
    · exact rck_lemmaH_of_parts (rck_lemmaH_E8 hg hβ).1 (rck_lemmaH_E8 hg hβ).2
    · exact rck_lemmaHC_tw (Or.inr (Or.inr rfl)) hg hβ
  · intro F _ _ σ g β hF hβ
    exact rck_lemmaH_of_parts (rck_lemmaH_triD4 hF hβ).1 (rck_lemmaH_triD4 hF hβ).2

@[expose] def RCKK2NbrRootSubShort :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R : Subgroup X) (t' : StatedLieTag) (m g : ℕ)
    (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' → 1 ≤ g → β ∈ (ggU t' m g).D.roots →
    ¬ GGLongRoot (ggU t' m g).D β → GGShortTag t' → 2 • β ∉ (ggU t' m g).D.roots →
    GGRootVia (ggU t' m g) K R β → ∀ r ∈ R, r ≠ 1 →
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X)

end CFSG.StandardType.RCKC1
