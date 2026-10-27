module

public import CFSG.Quasithin.Vol2.Ch11SecSSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def IsK0 {G : Type} [Group G] (T L V₁ K K₀ : Subgroup G) : Prop :=
  quasithinIsLocal T K₀ ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ LOf L V₁

@[expose] def Obl11_1_2StarAmalgam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ →
      pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥

@[expose] def Obl11_1_2StarShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ I₀ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ →
    pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥ →
    quasithinIsCComponent I₀ (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) →
    T ≤ Subgroup.normalizer (I₀ : Set G) → K₀ ≤ I₀ → LOf L V₂ ≤ I₀ → X ≤ I₀ →
      I₀ = K₀ ⊔ LOf L V₂ ∧ Shape11 I₀ 2

@[expose] def Obl11_1_2StarSL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → ¬ KindSL3 L (fsuV T I) 2

@[expose] def Obl11_1_2StarSym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ → ¬ KindSL3 L (fsuV T I) 2 →
    pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥ →
    quasithinIsCComponent (K₀ ⊔ LOf L V₂) (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) →
    T ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) →
    X ≤ K₀ ⊔ LOf L V₂ → Shape11 (K₀ ⊔ LOf L V₂) 2 →
      ∃ I' U₁ U₂ : Subgroup G, StarHyp G T (K₀ ⊔ LOf L V₂) I' U₁ U₂ X K ∧
        LOf (K₀ ⊔ LOf L V₂) U₁ = K₀ ∧ LOf (K₀ ⊔ LOf L V₂) U₂ = LOf L V₂

end CFSG.Quasithin.Vol2.Ch11.SecS
