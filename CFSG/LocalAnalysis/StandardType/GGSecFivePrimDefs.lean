module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Vocab

variable {G : Type} [Group G] [Finite G]

@[expose] def ggCoxRefl {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    (M : CoxeterMatrix ι) (e : M.Group ≃* ↥A) : Set (MulAut ↥Bs) :=
  {r | ∃ (w : M.Group) (i : ι), r = ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs)}

theorem ggCoxRefl_isReflection {p : ℕ} {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (h : ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M e) : GGIsReflection p r := by
  obtain ⟨w, i, rfl⟩ := hr
  have h1 : ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
      ((e w : ↥A) : MulAut ↥Bs) * ((e (M.simple i) : ↥A) : MulAut ↥Bs) *
        ((e w : ↥A) : MulAut ↥Bs)⁻¹ := by
    simp [map_mul, map_inv]
  rw [h1]
  exact (h i).conj _

end Vocab

section Inputs

@[expose] def GGSecFiveL1CoxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ggRankOnePerf Bs r = ggRankOneIn X Bs r

@[expose] def GGSecFiveRk1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
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
              (¬ GGSplitLie p X → p ∣ Nat.card F + 1)

@[expose] def GGSecFiveGenCoxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          X = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e},
            ggRankOneIn X Bs r

@[expose] def GGSecFiveOrbInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ i j : ι, M.M i j = 3 → GGOrbPair L Bs 𝒦 M e i j

@[expose] def GGSecFiveL2SplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ i j : ι, i ≠ j → M.M i j = 2 → ¬ GGOrbPair L Bs 𝒦 M e i j →
          ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
          ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            a * b = b * a

@[expose] def GGSecFiveRk2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
          ∀ r' ∈ ggAutomizer X Bs, r' ∈ ggCoxRefl M e → r ≠ r' →
            (r * r' = r' * r →
              ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
            (GGSplitLie p X → r * r' ≠ r' * r →
              ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
                LinearBlockStandardPair F W (ggRankOneIn X Bs r) (ggRankOneIn X Bs r'))

@[expose] def GGSecFiveSplitNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ K ∈ 𝒦, GGSplitLie p K

@[expose] def GGSecFiveJoinRegionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      (∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M)) →
      ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

end Inputs

end CFSG.StandardType
