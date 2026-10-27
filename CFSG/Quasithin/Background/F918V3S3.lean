module

public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.F918V3S3Aux

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem d392_component_case {M L A B₀ K X : Subgroup (MulAut W)} (hAM : A ≤ M)
    (hAL : ∀ a ∈ A, ∀ y ∈ L, a⁻¹ * y * a ∈ L)
    (hB₀A : B₀ ≤ A) (hB₀n : ∀ a ∈ A, ∀ b ∈ B₀, a * b * a⁻¹ ∈ B₀)
    (hK : IsComponentOf K M) (hKL : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x) (hKB : ⁅K, B₀⁆ ≠ ⊥)
    (hX : X = ⨆ a ∈ A, conjAutSub a K) :
    X ≠ ⊥ ∧ X ≤ M ∧ (∀ x ∈ X, ∀ y ∈ L, x * y = y * x) ∧
      A ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧ ⁅X, B₀⁆ = X :=
  F918V3S3.component_case_of_group hAM hAL hB₀A hB₀n hK hKL hKB hX

end CFSG.Quasithin
