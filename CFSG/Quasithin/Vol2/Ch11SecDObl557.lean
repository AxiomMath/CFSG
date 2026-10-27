module

public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl11_5_7SL3End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (x y : G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KindSL3 L (fsuV T I) n →
    ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →
    x ∈ L → y ∈ L → fsuV T I = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y → rconj V₁ x ⊓ rconj V₁ y = ⊥ →
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) ≤
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) x ⊓
        rconj (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) y →
    False

end CFSG.Quasithin.Vol2.Ch11.SecD
