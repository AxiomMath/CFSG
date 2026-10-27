module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Conjugating a commutator by an element that centralizes the first
factor gives the commutator of the conjugated pair. -/
public theorem conjugate_commutator_of_centralizes
    {G : Type u} [Group G] (z t y : G) (hzt : z * t * z⁻¹ = t) :
    z * (t * y * t⁻¹) * z⁻¹ =
      t * (z * y * z⁻¹) * t⁻¹ := by
  have hzt' : z * t = t * z := by
    calc
      z * t = (z * t * z⁻¹) * z := by group
      _ = t * z := by rw [hzt]
  have hzt_inv : t⁻¹ * z⁻¹ = z⁻¹ * t⁻¹ := by
    calc
      t⁻¹ * z⁻¹ = (z * t)⁻¹ := by simp
      _ = (t * z)⁻¹ := by rw [← hzt']
      _ = z⁻¹ * t⁻¹ := by simp
  calc
    z * (t * y * t⁻¹) * z⁻¹ = (z * t) * y * (t⁻¹ * z⁻¹) := by group
    _ = (t * z) * y * (z⁻¹ * t⁻¹) := by rw [hzt', hzt_inv]
    _ = t * (z * y * z⁻¹) * t⁻¹ := by group

public theorem centralizer_normalizes_commutator_closure
    {G : Type u} [Group G] (z t : G) (P : Subgroup G)
    (hzt : z * t * z⁻¹ = t)
    (hznorm : ∀ y : G, y ∈ P → z * y * z⁻¹ ∈ P) :
    ∀ y : G, y ∈ Subgroup.closure
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹} →
      z * y * z⁻¹ ∈ Subgroup.closure
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹} := by
  intro y hy
  refine Subgroup.closure_induction (k :=
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹}) ?mem ?one ?mul ?inv hy
  · intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    rw [conjugate_commutator_of_centralizes z t p hzt]
    exact Subgroup.subset_closure ⟨z * p * z⁻¹, hznorm p hp, rfl⟩
  · simpa using (Subgroup.closure
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹}).one_mem
  · intro x y _ _ hx hy
    have hzxy : z * (x * y) * z⁻¹ =
        (z * x * z⁻¹) * (z * y * z⁻¹) := by group
    rw [hzxy]
    exact (Subgroup.closure
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹}).mul_mem hx hy
  · intro x _ hx
    have hzxi : z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
    rw [hzxi]
    exact (Subgroup.closure
      {x : G | ∃ p : G, p ∈ P ∧ x = t * p * t⁻¹}).inv_mem hx

end CFSG.GorensteinWalter
