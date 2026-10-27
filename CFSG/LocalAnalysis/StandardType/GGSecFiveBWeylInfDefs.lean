module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

@[expose] def GGIsWeylMatrixBGe (k : ℕ) {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ℕ) (e : Fin n ≃ ι), k ≤ n ∧ M = (CoxeterMatrix.B n).reindex e

@[expose] def GGIsWeylMatrixBFour {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ e : Fin 4 ≃ ι, M = (CoxeterMatrix.B 4).reindex e

@[expose] def GGSecFiveBReflSatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixBGe 5 M →
          ∀ (hx : x ∈ Bs) (φ : MulAut ↥Bs), φ ∈ ggAInf p B Bs x L D J → GGIsReflection p φ →
            φ ⟨x, hx⟩ = ⟨x, hx⟩ → φ ∈ ggAutomizer L Bs

@[expose] def GGSecFiveBFourCoordSatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixBFour M →
          ∀ hx : x ∈ Bs, (∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧
              t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹) →
            ∀ φ : MulAut ↥Bs, φ ∈ ggAInf p B Bs x L D J → GGIsReflection p φ →
              φ ⟨x, hx⟩ = ⟨x, hx⟩ → φ ∈ ggAutomizer L Bs

@[expose] def GGSecFiveBFourPermWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixBFour M →
          ∀ hx : x ∈ Bs, (¬ ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧
              t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹) →
            GGWeylReflectionGroup p (ggAInf p B Bs x L D J)

end CFSG.StandardType

end
