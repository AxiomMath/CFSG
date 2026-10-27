module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin

@[expose] def SzCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsSz n X →
    ∀ α : MulAut X, (∃ e : ℕ, α ^ (3 ^ e) = 1) →
    ∀ S : Sylow 2 X, (∀ s ∈ (S : Subgroup X), α s ∈ (S : Subgroup X)) →
      (∀ b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), α b * b⁻¹ ∈ (S : Subgroup X)) →
      α = 1

@[expose] def SzEnd : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (L : Subgroup (MulAut W)) (U C : Subgroup W) (f : ℕ),
    BinaryNaturalSz L U C f → ∀ c : MulAut W, (∃ e : ℕ, c ^ (3 ^ e) = 1) →
      (∀ u ∈ U, c u ∈ U) → (∀ u ∈ C, c u ∈ C) → (∀ h ∈ L, c * h = h * c) →
      ∀ u ∈ U, c u * u⁻¹ ∈ C

end CFSG.Quasithin.H13.A6

