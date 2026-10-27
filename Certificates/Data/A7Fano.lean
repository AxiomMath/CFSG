module

public import Mathlib

public section

namespace CFSG.A7Fano

open Equiv
open scoped Pointwise

@[expose] def mkPerm7 (f g : Fin 7 → Fin 7) : Perm (Fin 7) :=
  if h : (∀ x, g (f x) = x) ∧ ∀ x, f (g x) = x then ⟨f, g, h.1, h.2⟩ else 1

@[expose] def fano1 : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2}}

@[expose] def fano2 : Finset (Finset (Fin 7)) :=
  {{0, 1, 5}, {1, 2, 6}, {2, 3, 0}, {3, 4, 1}, {4, 5, 2}, {5, 6, 3}, {6, 0, 4}}

@[expose] def cyc7 : Perm (Fin 7) := finRotate 7

@[expose] def dbl7 : Perm (Fin 7) := mkPerm7 ![0, 2, 4, 6, 1, 3, 5] ![0, 4, 1, 5, 2, 6, 3]

@[expose] def tau7 : Perm (Fin 7) := mkPerm7 ![0, 6, 5, 4, 3, 2, 1] ![0, 6, 5, 4, 3, 2, 1]

@[expose] def reps1_0 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 3, 4, 5, 6] ![0, 1, 2, 3, 4, 5, 6]

@[expose] def reps1_1 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 3, 5, 6, 4] ![0, 1, 2, 3, 6, 4, 5]

@[expose] def reps1_2 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 3, 6, 4, 5] ![0, 1, 2, 3, 5, 6, 4]

@[expose] def reps1_3 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 4, 5, 3, 6] ![0, 1, 2, 5, 3, 4, 6]

@[expose] def reps1_4 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 4, 6, 5, 3] ![0, 1, 2, 6, 3, 5, 4]

@[expose] def reps1_5 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 5, 3, 4, 6] ![0, 1, 2, 4, 5, 3, 6]

@[expose] def reps1_6 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 5, 4, 6, 3] ![0, 1, 2, 6, 4, 3, 5]

@[expose] def reps1_7 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 6, 3, 5, 4] ![0, 1, 2, 4, 6, 5, 3]

@[expose] def reps1_8 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 2, 6, 4, 3, 5] ![0, 1, 2, 5, 4, 6, 3]

@[expose] def reps1_9 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 3, 4, 2, 5, 6] ![0, 1, 4, 2, 3, 5, 6]

@[expose] def reps1_10 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 3, 5, 4, 2, 6] ![0, 1, 5, 2, 4, 3, 6]

@[expose] def reps1_11 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 3, 6, 4, 5, 2] ![0, 1, 6, 2, 4, 5, 3]

@[expose] def reps1_12 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 4, 2, 3, 5, 6] ![0, 1, 3, 4, 2, 5, 6]

@[expose] def reps1_13 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 5, 2, 4, 3, 6] ![0, 1, 3, 5, 4, 2, 6]

@[expose] def reps1_14 : Equiv.Perm (Fin 7) := mkPerm7 ![0, 1, 6, 2, 4, 5, 3] ![0, 1, 3, 6, 4, 5, 2]

@[expose] def reps1 : Fin 15 → Equiv.Perm (Fin 7) :=
  ![reps1_0, reps1_1, reps1_2, reps1_3, reps1_4, reps1_5, reps1_6, reps1_7,
    reps1_8, reps1_9, reps1_10, reps1_11, reps1_12, reps1_13, reps1_14]

@[expose] def stabSet (P : Finset (Finset (Fin 7))) : Finset (Perm (Fin 7)) :=
  Finset.univ.filter fun g => Perm.sign g = 1 ∧ g • P = P

@[expose] def fixCount (P : Finset (Finset (Fin 7))) (r : Fin 15 → Perm (Fin 7)) (j : Fin 15) :
    ℕ :=
  let I := (stabSet P).filter fun g => ((r j)⁻¹ * g * r j) • P = P
  (Finset.univ.filter fun i : Fin 15 => ∀ g ∈ I, ((r i)⁻¹ * g * r i) • P = P).card

@[expose] def normCount (σ : Perm (Fin 7)) : ℕ :=
  (Finset.univ.filter fun g : Perm (Fin 7) =>
    Perm.sign g = 1 ∧ (g * σ * g⁻¹ = σ ∨ g * σ * g⁻¹ = σ⁻¹)).card

end CFSG.A7Fano
