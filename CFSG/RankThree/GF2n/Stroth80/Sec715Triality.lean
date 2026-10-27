module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped Matrix

@[expose] def Omega8TrialityStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (H : Type) [Group H] (φ : H →* GL (Fin 4 ⊕ Fin 4) K),
    φ.range = StatedOmega (StatedQuadPlus 4 K) →
  ∀ (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X] (ρX : H →* (X ≃ₗ[K] X))
    (Y : Type) [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (ρY : H →* (Y ≃ₗ[K] Y)),
    (∀ h : H, φ h = 1 → ρX h = 1) → (∀ h : H, φ h = 1 → ρY h = 1) →
    (∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρX h x ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∀ S : Submodule K Y, (∀ h : H, ∀ y ∈ S, ρY h y ∈ S) → S = ⊥ ∨ S = ⊤) →
    Module.finrank K X = 8 → Module.finrank K Y = 8 →
  ∀ β : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K),
    (∀ (h : H) (x : X) (y : Y),
      β (ρX h x) (ρY h y) = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ β x y) →
    β ≠ 0 →
    (¬ ∃ e : X ≃ₗ[K] Y, ∀ (h : H) (x : X), e (ρX h x) = ρY h (e x)) ∧
    (¬ ∃ e : X ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K), ∀ (h : H) (x : X),
      e (ρX h x) = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ e x) ∧
    (¬ ∃ e : Y ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K), ∀ (h : H) (y : Y),
      e (ρY h y) = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ e y) ∧
    (∀ β' : X →ₗ[K] Y →ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      (∀ (h : H) (x : X) (y : Y),
        β' (ρX h x) (ρY h y) = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ β' x y) →
      ∃ c : K, β' = c • β) ∧
    (∀ β' : X →ₗ[K] X →ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      (∀ (h : H) (x x' : X),
        β' (ρX h x) (ρX h x') = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ β' x x') →
      β' = 0) ∧
    (∀ (Z : Type) [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z] (ρZ : H →* (Z ≃ₗ[K] Z))
      (Z' : Type) [AddCommGroup Z'] [Module K Z'] [FiniteDimensional K Z']
      (ρZ' : H →* (Z' ≃ₗ[K] Z')),
      (∀ h : H, φ h = 1 → ρZ h = 1) → (∀ h : H, φ h = 1 → ρZ' h = 1) →
      (∀ S : Submodule K Z, (∀ h : H, ∀ z ∈ S, ρZ h z ∈ S) → S = ⊥ ∨ S = ⊤) →
      (∀ S : Submodule K Z', (∀ h : H, ∀ z ∈ S, ρZ' h z ∈ S) → S = ⊥ ∨ S = ⊤) →
      Module.finrank K Z = 8 → Module.finrank K Z' = 8 →
      ∀ γ : Z →ₗ[K] Z' →ₗ[K] (Fin 4 ⊕ Fin 4 → K),
        (∀ (h : H) (z : Z) (z' : Z'),
          γ (ρZ h z) (ρZ' h z') = ((φ h : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K) *ᵥ γ z z') →
        γ ≠ 0 →
        ((∃ e : Z ≃ₗ[K] X, ∀ (h : H) (z : Z), e (ρZ h z) = ρX h (e z)) ∧
          ∃ e : Z' ≃ₗ[K] Y, ∀ (h : H) (z : Z'), e (ρZ' h z) = ρY h (e z)) ∨
        ((∃ e : Z ≃ₗ[K] Y, ∀ (h : H) (z : Z), e (ρZ h z) = ρY h (e z)) ∧
          ∃ e : Z' ≃ₗ[K] X, ∀ (h : H) (z : Z'), e (ρZ' h z) = ρX h (e z))) ∧
    (∃ qX : QuadraticForm K X, (∀ (h : H) (x : X), qX (ρX h x) = qX x) ∧
      ∀ x : X, (∀ x' : X, QuadraticMap.polar qX x x' = 0) → x = 0) ∧
    (∃ qY : QuadraticForm K Y, (∀ (h : H) (y : Y), qY (ρY h y) = qY y) ∧
      ∀ y : Y, (∀ y' : Y, QuadraticMap.polar qY y y' = 0) → y = 0) ∧
    ∀ (qX : QuadraticForm K X) (qY : QuadraticForm K Y),
      (∀ (h : H) (x : X), qX (ρX h x) = qX x) → (∀ (h : H) (y : Y), qY (ρY h y) = qY y) →
      qX ≠ 0 → qY ≠ 0 →
      (∀ y : Y, y ≠ 0 → qY y ≠ 0 → Module.finrank K (LinearMap.range (β.flip y)) = 8) ∧
      (∀ y : Y, y ≠ 0 → qY y = 0 → Module.finrank K (LinearMap.range (β.flip y)) = 4 ∧
        ∀ v ∈ LinearMap.range (β.flip y), StatedQuadPlus 4 K v = 0) ∧
      (∀ x : X, x ≠ 0 → qX x ≠ 0 → Module.finrank K (LinearMap.range (β x)) = 8) ∧
      (∀ x : X, x ≠ 0 → qX x = 0 → Module.finrank K (LinearMap.range (β x)) = 4 ∧
        ∀ v ∈ LinearMap.range (β x), StatedQuadPlus 4 K v = 0) ∧
      (∀ y : Y, y ≠ 0 → qY y = 0 → ∀ x ∈ LinearMap.ker (β.flip y), qX x = 0) ∧
      (∀ x : X, x ≠ 0 → qX x = 0 → ∀ y ∈ LinearMap.ker (β x), qY y = 0) ∧
      (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
        (LinearMap.range (β.flip y) = LinearMap.range (β.flip y') ∨
          LinearMap.ker (β.flip y) = LinearMap.ker (β.flip y')) → ∃ c : K, y' = c • y) ∧
      (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
        (LinearMap.range (β x) = LinearMap.range (β x') ∨
          LinearMap.ker (β x) = LinearMap.ker (β x')) → ∃ c : K, x' = c • x) ∧
      (∀ y y' : Y, y ≠ 0 → y' ≠ 0 → qY y = 0 → qY y' = 0 →
        Even (Module.finrank K ↥(LinearMap.range (β.flip y) ⊓ LinearMap.range (β.flip y')))) ∧
      (∀ x x' : X, x ≠ 0 → x' ≠ 0 → qX x = 0 → qX x' = 0 →
        Even (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β x')))) ∧
      ∀ (x : X) (y : Y), x ≠ 0 → y ≠ 0 → qX x = 0 → qY y = 0 →
        Odd (Module.finrank K ↥(LinearMap.range (β x) ⊓ LinearMap.range (β.flip y)))

@[expose] def Omega8EndScalarStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (H : Type) [Group H] (φ : H →* GL (Fin 4 ⊕ Fin 4) K),
    φ.range = StatedOmega (StatedQuadPlus 4 K) →
  ∀ (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (ρ : H →* (X ≃ₗ[K] X)), (∀ h : H, φ h = 1 → ρ h = 1) →
    (∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∃ h : H, ρ h ≠ 1) → Module.finrank K X ≤ 16 →
    ∀ T : X →ₗ[K] X, (∀ h : H, T ∘ₗ (ρ h : X →ₗ[K] X) = (ρ h : X →ₗ[K] X) ∘ₗ T) →
      ∃ c : K, T = c • LinearMap.id

end CFSG.RankThree.GF2n.Stroth80
