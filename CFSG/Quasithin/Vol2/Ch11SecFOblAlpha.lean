module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def Obl11_5_7Sp4Alpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ X : Subgroup G) (y : G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ → KindSp4 L (fsuV T I) n →
    ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →
    Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) →
    KOf L V₁ V₁ ≠ LOf L V₁ → IsCartanX T L X → y ∈ L → y ∈ Subgroup.normalizer (X : Set G) →
    conjSubgroup V₁ y ⊓ V₃ = ⊥ →
    pCoreOf 2 L ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) →
    ⁅V₃, pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))⁆ = ⊥ →
      ∃ Q₀ : Subgroup G, Q₀ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ∧ Q₀ ≠ ⊥ ∧
        (Q₀.subgroupOf (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))).Characteristic ∧
        conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊔
            conjSubgroup (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) y ≤
          Subgroup.normalizer (Q₀ : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecF
