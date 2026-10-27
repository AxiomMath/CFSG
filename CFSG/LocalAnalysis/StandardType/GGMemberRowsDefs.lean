module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan


section Vocab

variable {G : Type} [Group G] [Finite G]

@[expose] def GGRk1Concl (p : ℕ) (Bs X : Subgroup G) (r : MulAut ↥Bs) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
    Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
    (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
    (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
    (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F

@[expose] def GGPairConcl (Bs X : Subgroup G) (r r' : MulAut ↥Bs) : Prop :=
  (r * r' = r' * r →
    ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
  (r * r' ≠ r' * r →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
      Nat.card K = (2 ^ f) ^ 2 →
      Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs r'))

@[expose] def GGGenConcl {ι : Type} (M : CoxeterMatrix ι) (Bs X L : Subgroup G) (𝒦 : Finset (Subgroup G))
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) : Prop :=
  X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}, ggRankOneIn X Bs r

@[expose] def GGMemberUnitary (p : ℕ) (Bs X : Subgroup G) : Prop :=
  GGInnerDiagOnLabel
    (fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs X
end Vocab

@[expose] def GGRk1SplitMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs X r


@[expose] def GGRk1UnitaryMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs X r


@[expose] def GGRk1ResidualMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs X r


@[expose] def GGPairUnitaryMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' → GGPairConcl Bs X r r'


@[expose] def GGPairResidualMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' → GGPairConcl Bs X r r'

@[expose] def GGPairResidualMemberNInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' → GGPairConcl Bs X r r'

@[expose] def GGPairResidualMemberRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X → ¬ GGMemberUnitary p Bs X →
          ¬ GGInnerDiagOnLabel
            (fun p lab => (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ 2 ≤ lab.n) p Bs X →
          ¬ (X = L ∧ GGInnerDiagOnLabel
            (fun p lab => lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) p Bs X) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' → GGPairConcl Bs X r r'


@[expose] def GGGenUnitaryMemberInput : Prop :=
  GGSecFiveL1PhanInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          GGMemberUnitary p Bs X → GGMemberUnitary p Bs L →
          GGGenConcl M Bs X L 𝒦 e


@[expose] def GGGenResidualMemberInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          ¬ (GGMemberUnitary p Bs X ∧ GGMemberUnitary p Bs L) →
          GGGenConcl M Bs X L 𝒦 e

end CFSG.StandardType

end
