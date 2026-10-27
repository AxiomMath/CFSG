module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Layer

variable {G : Type} [Group G]

@[expose] def GGRootCentDerivedAtQ (p : ℕ) (G₀ : Subgroup G) (r : G) : Prop :=
  (∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y = 1) ∨
  (p ∣ Nat.card (ggRCSXd G₀ r) ∧
    (∃ Q : Subgroup G, Q ≤ ggRCSXd G₀ r ∧ IsPGroup 2 Q ∧ (Q.subgroupOf (ggRCSXd G₀ r)).Normal ∧
      ∀ [(Q.subgroupOf (ggRCSXd G₀ r)).Normal],
        CFSG.IsQuasisimple (↥(ggRCSXd G₀ r) ⧸ Q.subgroupOf (ggRCSXd G₀ r))) ∧
    ∀ y ∈ ggRCSX G₀ r, y ^ p = 1 → y ∈ ggRCSXd G₀ r)

@[expose] def GGRCSLayerQ (p : ℕ) (G₀ M : Subgroup G) (r : G) : Prop :=
  ∃ 𝒮₀ : Set (Subgroup G),
    (∀ S ∈ 𝒮₀, ∃ Q, GGRCSLayerQuasi p (M ⊓ Subgroup.centralizer {r}) S Q) ∧
    ∀ y ∈ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r}), y ^ p = 1 → y ∈ sSup 𝒮₀

@[expose] def GGRCSLayerNbr (p : ℕ) (G₀ M : Subgroup G) (r : G) : Prop :=
  GGRCSLayerQ p G₀ M r ∨ (p = 3 ∧ ∃ Q S T : Subgroup G, GGRCSSThreeSetting G₀ r Q S T)

@[expose] def GGRCSStructNbrConcl (p : ℕ) (G₀ M : Subgroup G) (r : G) : Prop :=
  ∃ 𝒮 : Set (Subgroup (GGRCSNbar r)),
    (∀ S ∈ 𝒮, GGRCSQuasiPiece p (ggRCSImg r M) S ∨
      (p = 3 ∧ GGRCSSThreePiece (ggRCSImg r M) S ∧ GGRCSNbr M r)) ∧
    ∀ y : ↥(Subgroup.centralizer ({r} : Set G)),
      (y : G) ∈ ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r}) → (y : G) ^ p = 1 →
        QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) y ∈
          sSup 𝒮

end Layer

section Inputs

@[expose] def GGRootCentSummandStructNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        GGRCSStructNbrConcl p (ggG0 p B x L D J) (ggM p B x L D J) r

@[expose] def GGRootCentDerivedQTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G)) →
    ((t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus) → n = 4 → f ≠ 1) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r → GGRootCentDerivedAtQ 3 ψ.range r

@[expose] def GGRootCentLayerNbrTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G)) →
    ((t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus) → n = 4 → f ≠ 1) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      GGRCSLayerNbr 3 ψ.range (Subgroup.normalizer (ψ.range : Set G)) r

end Inputs

end CFSG.StandardType
