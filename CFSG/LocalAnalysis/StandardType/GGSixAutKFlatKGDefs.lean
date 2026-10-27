module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatStepTwo
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Item1Statements

@[expose] def GGOTwoXi {G : Type} [Group G] (M E₀ : Subgroup G) (b : G) : Prop :=
  ∃ r : G, orderOf r = 2 ∧ r ∈ M ∧
    pCoreOf 2 (M ⊓ Subgroup.centralizer {b}) = Subgroup.zpowers r ∧
    r ∈ Subgroup.centralizer (E₀ : Set G) ∧
    pCoreOf 2 (M ⊓ Subgroup.centralizer {r}) ≤ Subgroup.zpowers r ∧
    ¬ IsPGroup 2 ↥(M ⊓ Subgroup.centralizer {r})

@[expose] def GGE0InnerDiagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G), b ∈ Bs → b ≠ 1 →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∀ C₀ : Subgroup G, IsComponentOf C₀ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
            D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (C₀ : Set G) ∧
            (LargeEvenMarking ↥C₀ (fun _ _ _ _ _ _ => True) →
              LargeEvenMarking ↥C₀ (fun lab _ _ I _ θ => GGChevStTag lab ∧
                ∀ ε ∈ D.map (MulAut.conj m⁻¹).toMonoidHom, ∃ φ ∈ I,
                  LargeEvenInduces θ (fun l l' => (l' : G) = ε⁻¹ * l * ε) φ))

@[expose] def GGOTwoCentralizerInputRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
        IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
        Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ ∨
            GGOTwoXi (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) b

end Item1Statements

section Item4Statements

variable {X : Type} [Group X]

@[expose] def GGRCSSummand (V E J : Subgroup X) : Prop :=
  J ≤ V ∧ IsSubnormal J V ∧ ⁅J, J⁆ = J ∧ pCoreOf 2 V ≤ J ∧ ⁅J, pCoreOf 2 V⁆ = pCoreOf 2 V ∧
    E ≤ Subgroup.normalizer (J : Set X) ∧
    ∀ [((pCoreOf 2 V).subgroupOf J).Normal],
      CFSG.Assembly.IsQuasisimple (↥J ⧸ (pCoreOf 2 V).subgroupOf J) ∧
      LargeEvenMarking (↥J ⧸ (pCoreOf 2 V).subgroupOf J) (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ∃ s s' : ↥J,
          QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧ (s' : X) = ε⁻¹ * s * ε) φ)

@[expose] def GGRCSStructKG (V E : Subgroup X) : Prop :=
  ∃ 𝒥 : Set (Subgroup X), (∀ P : Subgroup X, P ≤ V → ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
    ∀ J ∈ 𝒥, GGRCSSummand V E J

end Item4Statements

section Item4Input

@[expose] def GGRootCentStructKGInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        GGRCSStructKG (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E)

end Item4Input

end CFSG.StandardType
