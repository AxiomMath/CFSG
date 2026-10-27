module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def FactSp4Opp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ X : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → IsCartanX T L X →
      ∃ y ∈ L, y ∈ Subgroup.normalizer (X : Set G) ∧ conjSubgroup V₁ y ⊓ V₃ = ⊥

@[expose] def FactSp4Trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → ∀ y ∈ L, conjSubgroup V₁ y ⊓ V₃ = ⊥ →
    ∀ m ∈ Subgroup.normalizer (L : Set G), m ∈ Subgroup.normalizer (fsuV T I : Set G) →
      m ∈ Subgroup.normalizer (V₁ : Set G) → m ∈ Subgroup.normalizer (V₃ : Set G) →
        ∃ l ∈ LOf L V₁, conjSubgroup V₁ (y * m) = conjSubgroup V₁ (y * l)

@[expose] def FactSp4Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ X : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → IsCartanX T L X → ∀ P : Subgroup G, P ≤ ROf T L V₁ → ⁅V₃, P⁆ = ⊥ →
    ⁅fsuV T I, P⁆ ≠ ⊥ → X ≤ Subgroup.normalizer (P : Set G) → ∀ y ∈ L,
    conjSubgroup V₁ y ⊓ V₃ = ⊥ →
      L ≤ (LOf L V₁ ⊔ conjSubgroup P y) ⊔ pCoreOf 2 (L ⊔ T) ∧
        L ≤ conjClosure (conjSubgroup P y) L ⊔ pCoreOf 2 (L ⊔ T)

@[expose] def FactSp4RL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ X : Subgroup G),
    SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
    IsVi T L I n 3 V₃ → IsCartanX T L X → ∀ P : Subgroup G, P ≤ ROf T L V₁ →
    LOf L V₁ ≤ Subgroup.normalizer (P : Set G) → T ≤ Subgroup.normalizer (P : Set G) →
    X ≤ Subgroup.normalizer (P : Set G) → ⁅V₃, P⁆ ≠ ⊥ →
      pCoreOf 2 (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤ ⁅P, LOf L V₁⁆ ⊔ pCoreOf 2 L

end CFSG.Quasithin.Vol2.Ch11.SecF
