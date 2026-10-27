module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Preds

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixBstarUnique (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ ggM p B x L D J → IsPGroup p P → Bs ≤ P →
    (∀ Q : Subgroup G, Q ≤ ggM p B x L D J → IsPGroup p Q → P ≤ Q → Q = P) →
    ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
      Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)

@[expose] def GGSixLinearCase (p : ℕ) (t : StatedLieTag) (n f : ℕ) : Prop :=
  5 ≤ p ∧ n = p ∧ ((t = .PSL ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ 2 ^ f + 1))

@[expose] def GGTypeAk (f : ℕ) (K : Subgroup G) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ (LieModel (↥K ⧸ Subgroup.center ↥K) .PSL m 2 f ∨
    LieModel (↥K ⧸ Subgroup.center ↥K) .PSU m 2 f)

variable {U : Type} [Group U]

@[expose] def GGSixTrialityCase (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G)
    (Δ : UniversalRootDatum U) (t : StatedLieTag) (n f : ℕ) (ψ : U →* G) (y : G) : Prop :=
  t = .POmegaPlus ∧ n = 4 ∧ p = 3 ∧ 3 ∣ 2 ^ f - 1 ∧ ¬ GGPsiInnerDiag Δ ψ y ∧
    LieModel (↥(LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {y})) ⧸
      Subgroup.center ↥(LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {y}))) .PSL 3 2 f

end Preds

@[expose] def GGSixNbrCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J →
      ∀ g ∈ Subgroup.centralizer (D : Set G), ∀ (y : G) (K : Subgroup G),
        GGNbr p B x D J y K → g ∈ Subgroup.normalizer (K : Set G)

section Inputs

@[expose] def GGSixCentralizerOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    ¬ p ∣ Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)) →
      Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G)))

@[expose] def GGSixCentreOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
      Odd (Nat.card (Subgroup.center ↥J)) ∧
        ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))

@[expose] def GGSixKdComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
      ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})

@[expose] def GGSixCentralizerJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
      Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J

@[expose] def GGSixComponentsNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
      ∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
        D ≤ Subgroup.normalizer (K : Set G)

@[expose] def GGSixInnerOnKdInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J →
    (∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K : Set G)) →
      ∀ d ∈ D, d ≠ 1 → ∀ X : Subgroup G, X ≤ Subgroup.centralizer {d} →
        X ≤ Subgroup.normalizer (ggKd p B x L D J d : Set G) →
        D ≤ Subgroup.normalizer (X : Set G) → Nat.Coprime p (Nat.card X) → ⁅X, D⁆ = X →
          X ≤ ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G)

@[expose] def GGSixInndiagNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J →
      ∀ d ∈ D, d ≠ 1 → Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤
        Subgroup.normalizer ((Bs ⊔ ggKd p B x L D J d ⊔
          Subgroup.centralizer (ggKd p B x L D J d : Set G) : Subgroup G) : Set G)

@[expose] def GGSchreierPerfectInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) →
      ∀ K : Subgroup G, K ≤ Subgroup.normalizer (G₀ : Set G) → ⁅K, K⁆ = K → K ≤ G₀

@[expose] def GGTwoSignalizerGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, IsPGroup p E → E ≤ Subgroup.normalizer (G₀ : Set G) →
    ∀ T : Subgroup G, T ≤ G₀ → T ≠ ⊥ → IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set G) →
      ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ G₀ ∧ Q₂ ≤ G₀ ∧ IsPGroup 2 Q₁ ∧ IsPGroup 2 Q₂ ∧
        E ≤ Subgroup.normalizer (Q₁ : Set G) ∧ E ≤ Subgroup.normalizer (Q₂ : Set G) ∧
        Q₁ ⊔ Q₂ = G₀

@[expose] def GGSixBstarUniqueV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J

@[expose] def GGSixLSixElevenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J → g ∉ ggM p B x L D J →
          GGSixLinearCase p t n f ∨
            GGSixTrialityCase p B x L D J (ggU t n f).D t n f ψ (g⁻¹ * b * g)

@[expose] def GGSixLSixTwelveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J → g ∉ ggM p B x L D J → GGSixLinearCase p t n f →
          Nat.card Bs = p ^ (p - 1) ∧ ∀ K : Subgroup G,
            IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) → ¬ GGTypeAk f K

@[expose] def GGSixTrialityInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J →
    (∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J →
        GGSixTrialityCase p B x L D J (ggU t n f).D t n f ψ (g⁻¹ * b * g) →
          g ∈ ggM p B x L D J

@[expose] def GGSixLinearJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    Nat.card Bs = p ^ (p - 1) →
      ∀ d ∈ D, d ≠ 1 → ∃ K : Subgroup G,
        IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) ∧ GGTypeAk f K

end Inputs

end CFSG.StandardType
