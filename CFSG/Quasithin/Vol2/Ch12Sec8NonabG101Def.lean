module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

structure G101Hyp {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  alt : ∀ v, B v v = 0
  nondegenerate : ∀ v, (∀ w, B v w = 0) → v = 0
  isometry : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w
  point : v₁ ≠ 0
  isotropic : ∀ w ∈ W, ∀ w' ∈ W, B w w' = 0
  mem_W : v₁ ∈ W
  X_le : X ≤ Γ
  X_fixes : ∀ x ∈ X, x v₁ = v₁
  X_comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  X_sq : ∀ x ∈ X, x * x = 1
  X₀_le : X₀ ≤ X
  span_orbit : Submodule.span (ZMod 2) (MulAction.orbit Γ v₁) = ⊤
  odd_index : Odd (MulAction.stabilizer Γ v₁).index
  rank : Module.finrank (ZMod 2) W + Nat.log 2 (X₀.relIndex X) = Module.finrank (ZMod 2) V - 1
  commutator_le : ∀ x ∈ X, ∀ v, B v₁ v = 0 → x v - v ∈ W
  centralizer_le : ∀ x ∈ X, x ∉ X₀ → ∀ v, x v = v → B v₁ v = 0
  transvection : ∀ x ∈ X, ∃ f : W →ₗ[ZMod 2] ZMod 2, f ⟨v₁, mem_W⟩ = 0 ∧
    ∀ w : W, x (w : V) = (w : V) + f w • v₁
  transvection_full : ∀ f : W →ₗ[ZMod 2] ZMod 2, f ⟨v₁, mem_W⟩ = 0 →
    ∃ x ∈ X, ∀ w : W, x (w : V) = (w : V) + f w • v₁

structure G111Hyp {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop
    extends G101Hyp B Γ v₁ W X X₀ where
  three : (∀ v : V, (∀ x ∈ X, x v = v) → v = 0 ∨ v = v₁) ∨
    ∃ a ∈ X, Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 ∧
      v₁ ∈ LinearMap.range (a.toLinearMap - LinearMap.id)
  four : ∃ S : Subgroup (V ≃ₗ[ZMod 2] V),
    IsSylowTwoOf S (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁) ∧ X ≤ S ∧
      S ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V))

end CFSG.Quasithin
