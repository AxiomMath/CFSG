module

public import CFSG.Quasithin.Vol2.Ch10StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def FactXIrred : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      ∀ Y : Subgroup G, pCoreOf 2 (Xz T L (v₁ * v₂)) ≤ Y → Y ≤ Xz T L (v₁ * v₂) →
        T ≤ Subgroup.normalizer (Y : Set G) →
          Y = pCoreOf 2 (Xz T L (v₁ * v₂)) ∨ Y = Xz T L (v₁ * v₂)

@[expose] def FactXThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      Xz T L (v₁ * v₂) ≤ oPrimeResidualOf 3 (Xz T L (v₁ * v₂))

end CFSG.Quasithin.Vol2.Ch10.SecD
