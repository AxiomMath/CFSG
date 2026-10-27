module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoDPatterns

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

section Defs

variable {G : Type} [Group G]

@[expose] def qtwoRefl {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) {m : ℕ} (e' : Fin m ≃ ι) (i : Fin m) :
    MulAut ↥Bs :=
  ((e (M.simple (e' i)) : ↥A) : MulAut ↥Bs)

end Defs

section Inputs


@[expose] def GGQTwoDCfg {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)) {ι : Type} (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) : Prop :=
  GGSecFiveRouteCfg p B Bs x L D J 𝒦 ∧ ¬ GGSecFiveTier1Region p B Bs x L D J ∧
    ¬ GGSplitLie p L ∧ GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧
    ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6

@[expose] def GGQTwoL1InputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
          ∀ r : MulAut ↥Bs, r ∈ ggAutomizer X Bs → r ∈ ggCoxRefl M e →
            ggRankOne Bs r = ggRankOneIn X Bs r ∧ Nat.card ↥(ggRankOne Bs r) = 6

@[expose] def GGQTwoL1Input : Prop :=
  GGQTwoL1InputOn fun m => 7 ≤ m

@[expose] def GGQTwoEdgeAmbientInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs,
            r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn X Bs r r'

@[expose] def GGQTwoEdgeAmbientInput : Prop :=
  GGQTwoEdgeAmbientInputOn fun m => 7 ≤ m

@[expose] def QTwoMemberFacts {G : Type} [Group G] [Finite G] (Bs X : Subgroup G)
    {ι : Type} (M : CoxeterMatrix ι) (A : Subgroup (MulAut ↥Bs)) (e : M.Group ≃* ↥A) :
    Prop :=
  (∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ggRankOne Bs r = ggRankOneIn X Bs r) ∧
  (∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e →
    r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn X Bs r r') ∧
  (∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e →
    r * r' ≠ r' * r → Nat.card ↥(ggRankOneIn X Bs r) = 6 →
      UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn X Bs r r')
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs r')) ∧
  (∀ r₁ ∈ ggAutomizer X Bs, r₁ ∈ ggCoxRefl M e → ∀ r₂ ∈ ggAutomizer X Bs, r₂ ∈ ggCoxRefl M e →
    ∀ r₃ ∈ ggAutomizer X Bs, r₃ ∈ ggCoxRefl M e →
      r₁ * r₂ ≠ r₂ * r₁ → r₂ * r₃ ≠ r₃ * r₂ → r₁ * r₃ = r₃ * r₁ → r₁ ≠ r₃ →
        Nat.card ↥(ggRankOneIn X Bs r₁) = 6 →
          ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
            θ.range = ggRankTwoIn X Bs r₁ r₂ ⊔ ggRankTwoIn X Bs r₂ r₃) ∧
  (∀ r₁ ∈ ggAutomizer X Bs, r₁ ∈ ggCoxRefl M e → ∀ r₂ ∈ ggAutomizer X Bs, r₂ ∈ ggCoxRefl M e →
    ∀ r₃ ∈ ggAutomizer X Bs, r₃ ∈ ggCoxRefl M e →
    ∀ r₄ ∈ ggAutomizer X Bs, r₄ ∈ ggCoxRefl M e →
      r₁ * r₂ ≠ r₂ * r₁ → r₃ * r₄ ≠ r₄ * r₃ → r₁ * r₃ = r₃ * r₁ → r₁ * r₄ = r₄ * r₁ →
        r₂ * r₃ = r₃ * r₂ → r₂ * r₄ = r₄ * r₂ →
          ∀ x ∈ ggRankTwoIn X Bs r₁ r₂, ∀ y ∈ ggRankTwoIn X Bs r₃ r₄, x * y = y * x)

@[expose] def GGQTwoGenInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        (⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs (qtwoRefl e e') i j) =
          ggG0 p B x L D J

@[expose] def GGQTwoGenInput : Prop :=
  GGQTwoGenInputOn fun m => 7 ≤ m

end Inputs

end CFSG.StandardType.QTwo

end
