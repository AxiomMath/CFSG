module

public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def IsInducedOn {X W : Type*} [Group X] [Group W] (ρ : X →* MulAut W) (α : X ≃* X) :
    Prop :=
  ∃ φ : MulAut W, ∀ x : X, ρ (α x) = φ * ρ x * φ⁻¹

@[expose] def IsNatRealized {W : Type*} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    ((FFModel.nat (StatedSL 3 K)).Realizes H ⊤ ⊥ ∨ (FFModel.nat (StatedSp 2 K)).Realizes H ⊤ ⊥ ∨
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H ⊤ ⊥)

@[expose] def FactTwist : Prop :=
  ∀ (X W : Type) [Group X] [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (ρ : X →* MulAut W) (n : ℕ), 2 ≤ n → IsNatRealized ρ.range n →
      ∀ α₁ α₂ : X ≃* X, (∀ x, x ∈ ρ.ker ↔ α₁ x ∈ ρ.ker) → (∀ x, x ∈ ρ.ker ↔ α₂ x ∈ ρ.ker) →
        ¬ IsInducedOn ρ α₁ → ¬ IsInducedOn ρ α₂ → IsInducedOn ρ (α₂.trans α₁)

end CFSG.Quasithin.Vol2.Ch11.SecA
