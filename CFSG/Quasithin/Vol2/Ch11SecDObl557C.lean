module

public import CFSG.Quasithin.Vol2.Ch11SecDObl557B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl11_5_7SL3BigCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G) (x y : G),
    Config11_5_7SL3 G T L I n V₁ x y → KOf L V₁ V₁ = LOf L V₁ →
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ L →
    pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) = fsuV T I →
    Nat.card ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) = 2 ^ (5 * n) →
    pCoreOf 2 L = fsuV T I → False

end CFSG.Quasithin.Vol2.Ch11.SecD
