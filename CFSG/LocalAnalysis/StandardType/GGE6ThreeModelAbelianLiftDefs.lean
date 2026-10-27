module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType

@[expose] def GGNoInvFunc {L R : Type} [Group L] [Group R] (ψ : L →* R) (N : Set L)
    (V : Subgroup R) : Prop :=
  ∀ f : V →* Multiplicative (ZMod 3),
    (∀ n ∈ N, ∀ v v' : V, (v' : R) = ψ n * v * (ψ n)⁻¹ → f v' = f v) → f = 1

@[expose] def GGNoInvAlt {L R : Type} [Group L] [Group R] (ψ : L →* R) (N : Set L)
    (V : Subgroup R) : Prop :=
  ∀ κ : V → V → Multiplicative (ZMod 3),
    (∀ x y z, κ (x * y) z = κ x z * κ y z) → (∀ x y z, κ x (y * z) = κ x y * κ x z) →
    (∀ x, κ x x = 1) →
    (∀ n ∈ N, ∀ x y x' y' : V, (x' : R) = ψ n * x * (ψ n)⁻¹ → (y' : R) = ψ n * y * (ψ n)⁻¹ →
      κ x' y' = κ x y) →
    ∀ x y, κ x y = 1

@[expose] def GGAbelianLift : Prop :=
  ∀ (L R : Type) [Group L] [Group R] [Finite L] (ψ : L →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L → (Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3) →
    ∀ (T : Subgroup R) (N : Set L), (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
      (∀ n ∈ N, ∀ t ∈ T, ψ n * t * (ψ n)⁻¹ ∈ T) →
      GGNoInvFunc ψ N T → GGNoInvAlt ψ N T →
      ∀ A : Subgroup (MulAut L), IsPGroup 3 A →
        (∀ a ∈ A, ∀ l : L, ψ l ∈ T → ψ (a l) = ψ l) →
        (∀ a ∈ A, ∀ n ∈ N, ψ (n⁻¹ * a n) ∈ T) →
        (∀ x ∈ T.comap ψ, ∀ y ∈ T.comap ψ, x * y = y * x) ∧
        (∀ a ∈ A, ∀ x ∈ T.comap ψ, a x = x) ∧
        ∀ V₀ : Subgroup R, V₀ ≤ T → (∀ v ∈ V₀, v ^ 3 = 1) →
          (∀ n ∈ N, ∀ v ∈ V₀, ψ n * v * (ψ n)⁻¹ ∈ V₀) → GGNoInvFunc ψ N V₀ →
          ∀ t : L, ψ t ∈ V₀ → t ^ 3 = 1

end CFSG.StandardType
