module

public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.FormsBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀)

structure Co2McLFacts : Prop where
  perfect_co2 : ∀ u ∈ co1Orbit 0, ⁅co1Stab u, co1Stab u⁆ = co1Stab u
  perfect_mcl : ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
    ⁅co1Stab u ⊓ co1Stab v, co1Stab u ⊓ co1Stab v⁆ = co1Stab u ⊓ co1Stab v
  comm_span_co2 : ∀ u ∈ co1Orbit 0, ∀ X : Submodule (ZMod 2) (Fin 24 → ZMod 2),
    (∀ x ∈ X, bil₀ x u = 0) → (∀ A ∈ co1Stab u, ∀ x ∈ X, co1Act A x ∈ X) →
    (∀ A ∈ co1Stab u, ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → co1Act A y + y ∈ X) →
    ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → y ∈ X
  comm_span_mcl : ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
    ∀ X : Submodule (ZMod 2) (Fin 24 → ZMod 2),
    (∀ x ∈ X, bil₀ x u = 0 ∧ bil₀ x v = 0) →
    (∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ x ∈ X, co1Act A x ∈ X) →
    (∀ A ∈ co1Stab u ⊓ co1Stab v, ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → bil₀ y v = 0 →
      co1Act A y + y ∈ X) →
    ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → bil₀ y v = 0 → y ∈ X
  irred_co2 : ∀ u ∈ co1Orbit 0, ∀ Y : Submodule (ZMod 2) (Fin 24 → ZMod 2), u ∈ Y →
    (∀ y ∈ Y, bil₀ y u = 0) → (∀ A ∈ co1Stab u, ∀ y ∈ Y, co1Act A y ∈ Y) →
    Y = Submodule.span (ZMod 2) {u} ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y u = 0 → y ∈ Y
  nondeg_co2 : ∀ u ∈ co1Orbit 0, ∃ y₁ y₂ : Fin 24 → ZMod 2,
    bil₀ y₁ u = 0 ∧ bil₀ y₂ u = 0 ∧ bil₀ y₁ y₂ = 1
  nondeg_mcl : ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
    ∃ y₁ y₂ : Fin 24 → ZMod 2, bil₀ y₁ u = 0 ∧ bil₀ y₁ v = 0 ∧ bil₀ y₂ u = 0 ∧ bil₀ y₂ v = 0 ∧
      bil₀ y₁ y₂ = 1

end CFSG.Monster.GMS
