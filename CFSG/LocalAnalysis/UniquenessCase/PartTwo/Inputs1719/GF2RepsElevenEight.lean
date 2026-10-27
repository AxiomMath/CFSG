module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def W4Lem11_8Rk : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)), L ≤ Y → (L.subgroupOf Y).Normal →
      IsSpor ↥L .J2 → IsIrrOn L ⊤ ⊥ → E3.mParam Y < 8 → rk W = 12

@[expose] def K_J2InvertsGen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal → IsSpor ↥K .J2 →
    ∀ a : Y, a * a = 1 → (∃ k ∈ K, a * k ≠ k * a) →
      ∃ x ∈ K, ∃ g ∈ K,
        (orderOf (x⁻¹ * (a * x * a⁻¹)) = 5 ∨ orderOf (x⁻¹ * (a * x * a⁻¹)) = 7) ∧
          Subgroup.closure {x⁻¹ * (a * x * a⁻¹), g * (x⁻¹ * (a * x * a⁻¹)) * g⁻¹} = K

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
