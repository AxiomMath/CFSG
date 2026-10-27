module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.RonanG1016

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def InducesIsometries (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (f : LinearMap.BilinForm (ZMod 2) I) : Prop :=
  (∀ k ∈ K, ∀ x y x' y' : I, k (x : V) = (x' : V) → k (y : V) = (y' : V) → f x' y' = f x y) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x y, f (g x) (g y) = f x y) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def InducesSp (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ f : LinearMap.BilinForm (ZMod 2) I, (∀ x, f x x = 0) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
    InducesIsometries K I f

@[expose] def InducesOrth (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ q : I → ZMod 2, (∀ (c : ZMod 2) x, q (c • x) = c * c * q x) ∧
    (∃ B' : LinearMap.BilinForm (ZMod 2) I, (∀ x y, q (x + y) = q x + q y + B' x y) ∧
      (∀ x, (∀ y, B' x y = 0) → x = 0)) ∧
    (∀ k ∈ K, ∀ x x' : I, k (x : V) = (x' : V) → q x' = q x) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x, q (g x) = q x) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def IsSymNaturalSub (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (φ : ↥K ≃* Equiv.Perm (Fin n)) (β : ↥(permCore n) →ₗ[ZMod 2] ↥I),
    Function.Surjective β ∧
    (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    ∀ (γ : ↥K) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct (φ γ) (u : Fin n → ZMod 2) →
        ((β u' : I) : V) = (γ : GLV V) ((β u : I) : V)

end CFSG.Quasithin.RonanG1016
