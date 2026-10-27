module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

@[expose] def IsSignedCoords {Y : Type} [Group Y] (A : Subgroup Y)
    (c : Multiplicative (Fin 3 → ZMod 3) →* Y) : Prop :=
  Function.Injective c ∧ c.range = A ∧
    (∀ n ∈ normalizer (A : Set Y), ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3),
      (∀ i, ε i ≠ 0) ∧ ∀ v, n * c v * n⁻¹ =
        c (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i))) ∧
    (∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) → ∃ n : Y, ∀ v,
      n * c v * n⁻¹ = c (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)))

@[expose] def IsSumZeroCoords {Y : Type} [Group Y] (A : Subgroup Y)
    (c : Multiplicative (Fin 4 → ZMod 3) →* Y) : Prop :=
  c.range = A ∧ (∀ v, c v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t) ∧
    (∀ n ∈ normalizer (A : Set Y), ∃ σ : Equiv.Perm (Fin 4), ∀ v, n * c v * n⁻¹ =
      c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i))) ∧
    (∀ σ : Equiv.Perm (Fin 4), ∃ n : Y, ∀ v,
      n * c v * n⁻¹ = c (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
