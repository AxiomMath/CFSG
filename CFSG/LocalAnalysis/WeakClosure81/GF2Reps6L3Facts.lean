module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup

@[expose] def derivedCent {X : Type*} [Group X] (t : X) : Subgroup X :=
  ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆

structure L3OddPointed (X : Type*) [Group X] (t₀ : X) : Prop where
  orderOf_eq : orderOf t₀ = 2
  conj : ∀ t : X, orderOf t = 2 → ∃ g : X, g * t₀ * g⁻¹ = t
  inner : ∀ B : Subgroup (MulAut X), Nat.card B = 4 → (∀ β ∈ B, β * β = 1) →
    ∃ β ∈ B, β ≠ 1 ∧ β ∈ (MulAut.conj : X →* MulAut X).range
  quasi : CFSG.Open.IsQuasisimple ↥(derivedCent t₀)
  cent : ∀ β : MulAut X, β * β = 1 → β t₀ = t₀ → (∀ k ∈ derivedCent t₀, β k = k) →
    β = 1 ∨ β = MulAut.conj t₀
  gen : ∀ t : X, orderOf t = 2 → t₀ * t = t * t₀ → t₀ ≠ t →
    derivedCent t₀ ⊔ derivedCent t = ⊤
  four : ∃ g : X, orderOf (t₀ * (g * t₀ * g⁻¹)) = 4

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
