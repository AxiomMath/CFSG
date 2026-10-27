module

public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Config11_5_7SL3 (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ)
    (V₁ : Subgroup G) (x y : G) : Prop :=
  Hyp11 G T L I n ∧ IsVi T L I n 1 V₁ ∧ KindSL3 L (fsuV T I) n ∧
    ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ∧
    x ∈ L ∧ y ∈ L ∧ fsuV T I = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y ∧ rconj V₁ x ⊓ rconj V₁ y = ⊥ ∧
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) x ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) y ∧
    (∀ a ∈ pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))),
      ∀ b ∈ pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))),
        a * b = b * a) ∧
    (∀ a ∈ pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))),
      a ^ 2 = 1) ∧
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      fsuV T I ⊔ (pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ⊓
        Subgroup.centralizer (L : Set G)) ∧
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
      (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓ L) ⊔
        (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
          Subgroup.centralizer (L : Set G)) ∧
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (L : Set G) ≤
      pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

@[expose] def Obl11_5_7SL3Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (x y : G),
    Config11_5_7SL3 G T L I n V₁ x y → KOf L V₁ V₁ ≠ LOf L V₁ → False

@[expose] def Obl11_5_7SL3Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (x y : G),
    Config11_5_7SL3 G T L I n V₁ x y → KOf L V₁ V₁ = LOf L V₁ → False

end CFSG.Quasithin.Vol2.Ch11.SecD
