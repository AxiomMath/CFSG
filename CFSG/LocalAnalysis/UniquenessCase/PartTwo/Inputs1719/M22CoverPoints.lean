module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def K_M22CoverNine : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    IsSpor (↥K ⧸ Subgroup.center ↥K) .M22 → Subgroup.center ↥K ≠ ⊥ →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S

@[expose] def K_M22TenPointThree : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) → Nat.card W = 2 ^ 10 →
    ∀ L : Subgroup (MulAut W), IsSpor ↥L .M22 →
      (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      ∀ w : W, w ≠ 1 → ∃ g ∈ L, orderOf g = 3 ∧ g w = w

@[expose] def K_M22ReducibleBound : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)), L ≤ Y → (L.subgroupOf Y).Normal → IsSpor ↥L .M22 →
      fixV L = ⊥ → (⨆ I ∈ irrSet L, I) = ⊤ → ¬ IsIrrOn L ⊤ ⊥ →
        bParam L Y + 3 ≤ E3.mParam Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
