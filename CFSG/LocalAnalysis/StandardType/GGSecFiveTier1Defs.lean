module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

@[expose] def GGIsWeylMatrixAD {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (n : ℕ) (e : Fin n ≃ ι), 3 ≤ n ∧ M = (CoxeterMatrix.A n).reindex e) ∨
    (∃ (n : ℕ) (e : Fin n ≃ ι), 4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e)

section Inputs

@[expose] def GGSecFiveTier1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), CharP F 2 ∧ 4 ≤ Nat.card F ∧
          (∀ i j : ι, i ≠ j → M.M i j = 2 →
            ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
            ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
              a * b = b * a) ∧
          (∀ i j : ι, M.M i j = 3 → ∃ W : Subgroup G, LinearBlockStandardPair F W
            (ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
            (ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))) ∧
          ⨆ i, ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
            L ⊔ ⨆ K ∈ 𝒦, K

theorem ggSecFiveWeakCTInput_of_tier1 (h : GGSecFiveTier1Input) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
          ∃ (F : Type) (_ : Field F) (_ : Finite F), 4 ≤ Nat.card F ∧
            (∀ i j : ι, i ≠ j → M.M i j = 2 →
              ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
              ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
                a * b = b * a) ∧
            (∀ i j : ι, M.M i j = 3 → ∃ W : Subgroup G, LinearBlockStandardPair F W
              (ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
              (ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))) ∧
            ⨆ i, ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
              L ⊔ ⨆ K ∈ 𝒦, K := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hsl
  obtain ⟨F, hF, hfin, -, h4, hcomm, hpair, hgen⟩ :=
    h G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hsl
  exact ⟨F, hF, hfin, h4, hcomm, hpair, hgen⟩

@[expose] def GGSecFiveIdentADInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixAD M →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
            GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ

@[expose] def GGSecFiveIdentRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ (GGSplitLie p L ∧ ∃ (ι : Type) (M : CoxeterMatrix ι)
          (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ GGIsWeylMatrixAD M) →
        ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
          GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ

end Inputs

end CFSG.StandardType

end
