module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGPhanCentralQuotient
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

open scoped MatrixGroups

@[expose] def GGSecFiveL1PhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ggRankOnePerf Bs r = ggRankOneIn X Bs r

@[expose] def GGSecFiveRk1PhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∃ (F : Type) (_ : Field F) (_ : Finite F)
              (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
              Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
              (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
                ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
              (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
              (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
              ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
                GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F

@[expose] def GGSecFiveRk1PhanNInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∃ (F : Type) (_ : Field F) (_ : Finite F)
              (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
              Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
              (∃ n ∈ ggRankOneIn X Bs r, n ∈ Subgroup.normalizer (Bs : Set G) ∧
                ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
              (GGSplitLie p X → p ∣ Nat.card F - 1) ∧
              (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
              ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
                GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F

@[expose] def GGSecFiveGenPhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
            ggRankOneIn X Bs r

@[expose] def GGSecFiveGenPhanNInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
            ggRankOneIn X Bs r

@[expose] def GGSecFiveOrbPhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, M.M i j = 3 → GGOrbPair L Bs 𝒦 M e i j

@[expose] def GGSecFiveL2PhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
          ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            a * b = b * a

@[expose] def GGSecFiveL2PhanDEInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (GGIsWeylMatrixD M ∨ GGIsWeylMatrixE M) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
          ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            a * b = b * a

@[expose] def GGSecFivePhanPairInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' →
            (r * r' = r' * r →
              ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
            (r * r' ≠ r' * r →
              ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
                Nat.card K = (2 ^ f) ^ 2 →
                Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
                ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
                  (ggRankOneIn X Bs r) (ggRankOneIn X Bs r'))

@[expose] def GGSecFivePhanPairNInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ¬ ((∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) ∧
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ¬ GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' →
            (r * r' = r' * r →
              ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
            (r * r' ≠ r' * r →
              ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
                Nat.card K = (2 ^ f) ^ 2 →
                Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
                ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
                  (ggRankOneIn X Bs r) (ggRankOneIn X Bs r'))

@[expose] def GGSecFiveNonSplitNbrInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∀ K ∈ 𝒦, ¬ GGSplitLie p K

@[expose] def GGSecFiveJoinPhanInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      (∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ GGIsWeylMatrixD M ∧
          ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
      ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

@[expose] def GGSecFiveDataResPhanDQTwoInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixD M →
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
        GGSecFiveData p B x L D J

end CFSG.StandardType

end
