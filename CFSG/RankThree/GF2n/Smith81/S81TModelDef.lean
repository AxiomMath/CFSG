module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

variable {K : Type} [Field K] {E' : Type} [AddCommGroup E'] [Module K E']

@[expose] def CwE (t : E' ≃ₗ[K] E') : Set E' := {c | t c = c}

@[expose] def RwE (t : E' ≃ₗ[K] E') : Set E' := {r | ∃ w, r = t w - w}

@[expose] def GcentE (Γ : Subgroup (E' ≃ₗ[K] E')) (t : E' ≃ₗ[K] E') : Set (E' ≃ₗ[K] E') :=
  {g | g ∈ Γ ∧ g * t = t * g}

structure InvolK12 (Γ : Subgroup (E' ≃ₗ[K] E')) (p₀ : E') (β' : E' → E' → K)
    (t : E' ≃ₗ[K] E') : Prop where
  qfR : ∀ v : E', β' (t v) v = 0
  covC : ∀ c ∈ CwE t, ∃ r ∈ RwE t, c - r ∈
    AddSubgroup.closure {v | ∃ g ∈ GcentE Γ t, ∃ c' ∈ CwE t, v = g c' - c'}
  P3 : ∃ U : Set (E' ≃ₗ[K] E'), (∀ u ∈ U, u ∈ GcentE Γ t) ∧
    (∀ u ∈ U, ∀ c ∈ CwE t, u c - c ∈ RwE t) ∧ ∀ c ∈ CwE t, (∀ u ∈ U, u c = c) → c ∈ RwE t
  P2 : ∀ S : AddSubgroup E', S ≠ ⊥ → (∀ s ∈ S, s ∈ RwE t) →
    (∀ a ∈ GcentE Γ t, ∀ b ∈ GcentE Γ t, ∀ s ∈ S, (a * b * a⁻¹ * b⁻¹) s ∈ S) →
    ∃ p ∈ S, p ≠ 0 ∧ ∃ g ∈ Γ, ∃ c : K, p = c • g p₀

structure InvolK3 (Γ : Subgroup (E' ≃ₗ[K] E')) (β' : E' → E' → K) (t : E' ≃ₗ[K] E') : Prop where
  CR : ∀ c ∈ CwE t, c ∈ RwE t
  qf_ne : ∃ v : E', β' (t v) v ≠ 0

end CFSG.RankThree.GF2n.Smith81.MinuscT
