module

public import CFSG.Monster.GMS.CoTwoFacts

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀ v₂)

structure McLRepFacts (c₁ c₂ : Co1) (y₀ : Fin 24 → ZMod 2) : Prop where
  mem_y₀ : y₀ ∈ co1Orbit 0
  sum_mem : v₂ + y₀ ∈ co1Orbit 1
  fix_c₁ : co1Act c₁ v₂ = v₂ ∧ co1Act c₁ y₀ = y₀
  fix_c₂ : co1Act c₂ v₂ = v₂ ∧ co1Act c₂ y₀ = y₀
  irred : ∀ Y : Submodule (ZMod 2) (Fin 24 → ZMod 2),
    (∀ y ∈ Y, bil₀ y v₂ = 0 ∧ bil₀ y y₀ = 0) → (∀ y ∈ Y, co1Act c₁ y ∈ Y) →
    (∀ y ∈ Y, co1Act c₂ y ∈ Y) →
    Y = ⊥ ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y v₂ = 0 → bil₀ y y₀ = 0 → y ∈ Y
  nontriv : ∃ y : Fin 24 → ZMod 2, bil₀ y v₂ = 0 ∧ bil₀ y y₀ = 0 ∧
    (co1Act c₁ y ≠ y ∨ co1Act c₂ y ≠ y)
  nondeg : ∃ y₁ y₂ : Fin 24 → ZMod 2, bil₀ y₁ v₂ = 0 ∧ bil₀ y₁ y₀ = 0 ∧ bil₀ y₂ v₂ = 0 ∧
    bil₀ y₂ y₀ = 0 ∧ bil₀ y₁ y₂ = 1

structure Co2McLModule : Prop where
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

theorem co2McLFacts_of
    (hperf₁ : ∀ u ∈ co1Orbit 0, ⁅co1Stab u, co1Stab u⁆ = co1Stab u)
    (hperf₂ : ∀ u ∈ co1Orbit 0, ∀ v ∈ co1Orbit 0, u + v ∈ co1Orbit 1 →
      ⁅co1Stab u ⊓ co1Stab v, co1Stab u ⊓ co1Stab v⁆ = co1Stab u ⊓ co1Stab v)
    (hM : Co2McLModule) : Co2McLFacts :=
  ⟨hperf₁, hperf₂, hM.comm_span_co2, hM.comm_span_mcl, hM.irred_co2, hM.nondeg_co2,
    hM.nondeg_mcl⟩

end CFSG.Monster.GMS
