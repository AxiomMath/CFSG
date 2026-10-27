module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

@[expose] def Input1469A5Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz K₁ K₂ Λ : Subgroup G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S 2 ![K₁, K₂] →
    IsAltType K₁ 5 → IsAltType K₂ 5 → ¬ K₁ ≤ Iz →
    HypC51 I Λ S S → S.relIndex Λ = 2 →
    (∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (Λ ⊔ I ≤ Subgroup.normalizer (R₀ : Set G))) →
    IsElemAbelian 2 (S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ∧
      S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ≤ centerOf (baum S)

end CFSG.Quasithin
