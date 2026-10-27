module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open SpCoord NbrOrth

structure OrthWeakFrame (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  [instChar : CharP F 2]
  V : Type
  [instAdd : AddCommGroup V]
  [instMod : Module F V]
  [instFD : FiniteDimensional F V]
  Q : QuadraticForm F V
  A : Subgroup (V ≃ₗ[F] V)
  r : ℕ
  Δ : TBJOmData Q p A r
  ψ : ↥(orthDerived Q) →* G
  β : ↥Bs →* ↥(orthDerived Q)
  f : ℕ
  hA : A ≤ orthDerived Q
  hr : 4 ≤ r
  hcard : Nat.card F = 2 ^ f
  hf : 2 ≤ f
  hpq : p ∣ Nat.card F + 1
  hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0
  hinj : Function.Injective ψ
  hrange : ψ.range = X
  hβA : ∀ b : ↥Bs, (β b : V ≃ₗ[F] V) ∈ A
  hβsurj : ∀ a ∈ A, ∃ b : ↥Bs, (β b : V ≃ₗ[F] V) = a
  hcompat : ∀ (b : ↥Bs) (y : ↥(orthDerived Q)), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹
  swapReal : ∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q),
    (∀ f' : Fin r → Multiplicative (ZMod p),
      (w : V ≃ₗ[F] V) * Δ.τ f' * (w : V ≃ₗ[F] V)⁻¹ = Δ.τ (permAut (Equiv.swap i j) f')) ∧
    ψ w ∈ Subgroup.normalizer (Bs : Set G)
  dinvReal : ∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q),
    (∀ f' : Fin r → Multiplicative (ZMod p),
      (w : V ≃ₗ[F] V) * Δ.τ f' * (w : V ≃ₗ[F] V)⁻¹ = Δ.τ (dinv i j f')) ∧
    ψ w ∈ Subgroup.normalizer (Bs : Set G)

attribute [instance] OrthWeakFrame.instField OrthWeakFrame.instFinite OrthWeakFrame.instChar
  OrthWeakFrame.instAdd OrthWeakFrame.instMod OrthWeakFrame.instFD

end OrthTorus

end CFSG.StandardType

end
