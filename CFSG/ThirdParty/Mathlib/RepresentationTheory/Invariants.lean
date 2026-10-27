/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# The averaging idempotent of a finite-group representation

Ported from `Mathlib/RepresentationTheory/Invariants.lean` (Mathlib, Apache 2.0, at the pinned
commit `b63f6e8a68d2`): `average`, `mul_average_left`, `mul_average_right`, `averageMap`,
`averageMap_invariant`, `averageMap_id` and `isProj_averageMap`. Local changes: the declarations
live in `Representation.GroupAlgebra` rather than in `GroupAlgebra` and `Representation`; `k` is a
field and `(Fintype.card G : k)⁻¹` replaces Mathlib's `⅟(Fintype.card G : k)`, so
`averageMap_id` and `isProj_averageMap` assume `CharZero k` instead of `Invertible`.
-/

public section

universe u v w

namespace Representation

namespace GroupAlgebra

open scoped MonoidAlgebra

-- Ported from Mathlib.RepresentationTheory.Invariants

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
variable {V : Type w} [AddCommGroup V] [Module k V]

@[expose] noncomputable def average (k : Type u) (G : Type v) [Field k] [Monoid G] [Fintype G] : k[G] :=
   ((Fintype.card G : k)⁻¹) • ∑ g : G, MonoidAlgebra.of k G g

@[simp]
theorem mul_average_left (g : G) :
    MonoidAlgebra.single g 1 * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => MonoidAlgebra.single x 1
  change ((Fintype.card G : k)⁻¹) • ∑ x : G, f (g * x) = ((Fintype.card G : k)⁻¹) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

@[simp]
theorem mul_average_right (g : G) :
    average k G * MonoidAlgebra.single g 1 = average k G :=  by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => MonoidAlgebra.single x 1
  change ((Fintype.card G : k)⁻¹) • ∑ x : G, f (x * g) = ((Fintype.card G : k)⁻¹)  • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[expose] noncomputable def averageMap (ρ : Representation k G V) : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
private theorem averageMap_invariant (ρ : Representation k G V) (v : V) :
    averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_apply,
    ← map_mul (asAlgebraHom ρ), mul_average_left]

/--
In characteristic zero, the averaging operator acts as the identity on invariant
vectors.
-/
private theorem averageMap_id [CharZero k]
    (ρ : Representation k G V) (v : V) (hv : v ∈ invariants ρ) :
    averageMap ρ v = v := by
  rw [mem_invariants] at hv
  have hcard : (Fintype.card G : k) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [averageMap, average, map_sum, hv, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k (Fintype.card G) v, smul_smul, hcard]

theorem isProj_averageMap [CharZero k] (ρ : Representation k G V) :
    LinearMap.IsProj ρ.invariants (averageMap ρ) := ⟨averageMap_invariant ρ, averageMap_id ρ⟩

end GroupAlgebra

end Representation
