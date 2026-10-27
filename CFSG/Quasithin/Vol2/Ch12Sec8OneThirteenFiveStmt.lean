module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def Lemma12_8_13_five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ K₁ : Subgroup G),
    Setting1282One G T L V 4 V₁ V₂ → lOne L V₁ ≤ K₁ →
    quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
    Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ D : HatModelU (u128 V V₁), G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))) →
      (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2 →
      Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K₁ : Set G) ∧
      quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥ ∧
      conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K₁ ≤ zU128 V V₁ ∧
      IsTwoReducedIn (K₁ ⊔ T)
        (conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K₁) ∧
      ⁅quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁), K₁⁆ ≠ ⊥ ∧
      K₁ = ⁅K₁, CFSG.conjugate (zU128 V V₁) g⁆ ∧
      quasithinIsFaithfulLocal T K₁

end CFSG.Quasithin.H13
