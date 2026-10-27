module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.RuTypeF4

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups

@[expose] def KGG22PointStab : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 6 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    Nat.card Γ = 12096 → ∀ v : V, v ≠ 0 →
    ∀ S Z₀ : Subgroup (V ≃ₗ[ZMod 2] V), S ≤ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v →
      Nat.card S = 64 → Z₀ ≤ S → Nat.card Z₀ = 2 →
      S ≤ Subgroup.normalizer (Z₀ : Set (V ≃ₗ[ZMod 2] V)) →
      ¬ Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v ≤
        Subgroup.normalizer (Z₀ : Set (V ≃ₗ[ZMod 2] V))

@[expose] def KGG22Rank : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 6 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    Nat.card Γ = 12096 → ∀ X : Subgroup (V ≃ₗ[ZMod 2] V), X ≤ Γ →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → (∀ x ∈ X, x * x = 1) → Nat.card X ≤ 8

@[expose] def KGSp4Quad : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 4 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    ∀ q : V → ZMod 2, (∀ v w, q (v + w) = q v + q w + B v w) → (∀ γ ∈ Γ, ∀ v, q (γ v) = q v) →
      Nat.card Γ ≤ 120

@[expose] def KGSp4Line : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V), (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    Module.finrank (ZMod 2) V = 4 →
    ∀ Γ : Subgroup (V ≃ₗ[ZMod 2] V), (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) →
    360 ≤ Nat.card Γ → ∀ v : V, v ≠ 0 →
    ∀ ℓ : Submodule (ZMod 2) V, v ∈ ℓ → Module.finrank (ZMod 2) ℓ = 2 →
      (∀ w ∈ ℓ, ∀ w' ∈ ℓ, B w w' = 0) →
      ∃ γ ∈ Γ, γ v = v ∧ ∃ w ∈ ℓ, γ w ∉ ℓ

@[expose] def KGL24Quad : Prop :=
  ∀ q : (Fin 2 → RuType.F4) → ZMod 2,
    (∃ β : (Fin 2 → RuType.F4) →+ (Fin 2 → RuType.F4) →+ ZMod 2,
      ∀ v w, q (v + w) = q v + q w + β v w) →
    (∀ (M : SL(2, RuType.F4)) (v : Fin 2 → RuType.F4),
      q ((M : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v) = q v) →
    ∀ v, q v = 0

end CFSG.Quasithin.H13
