module

public import CFSG.Sporadic.Recognition.LyonsLocalBasic

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm

@[expose] def invP1 : Perm (Fin 11) := swap 1 2 * swap 9 10

@[expose] def genP : Fin 3 → Perm (Fin 11) := ![invP1, swapP, swapP23]

@[expose] def wordP : List (Fin 3) → Perm (Fin 11)
  | [] => 1
  | i :: w => genP i * wordP w

@[expose] def e6p : Fin 6 → Perm (Fin 11) := ![x1p, x1p⁻¹, x2p, x2p⁻¹, x3p, x3p⁻¹]

@[expose] def e4p : Fin 4 → Perm (Fin 11) := ![x1p, x1p⁻¹, x2p, x2p⁻¹]

@[expose] def wordsA : List (List (Fin 3)) :=
  [[],
   [2, 1, 0, 1, 2],
   [1, 0, 1],
   [2, 1, 0, 1, 2, 1, 0, 1],
   [2],
   [1, 0, 1, 2],
   [2, 1, 0, 1],
   [1, 0, 1, 2, 1, 0, 1],
   [0],
   [2, 1, 0, 1, 2, 0],
   [1, 0, 1, 0],
   [2, 1, 0, 1, 2, 1, 0, 1, 0],
   [2, 0],
   [1, 0, 1, 2, 0],
   [2, 1, 0, 1, 0],
   [1, 0, 1, 2, 1, 0, 1, 0],
   [1],
   [2, 1, 0, 1, 2, 1],
   [0, 1],
   [2, 1, 0, 1, 2, 0, 1],
   [1, 2],
   [0, 1, 2],
   [1, 2, 1, 0, 1],
   [0, 1, 2, 1, 0, 1],
   [1, 0],
   [2, 1, 0, 1, 2, 1, 0],
   [0, 1, 0],
   [2, 1, 0, 1, 2, 0, 1, 0],
   [1, 2, 0],
   [0, 1, 2, 0],
   [1, 2, 1, 0, 1, 0],
   [0, 1, 2, 1, 0, 1, 0],
   [2, 1],
   [1, 0, 1, 2, 1],
   [2, 0, 1],
   [1, 0, 1, 2, 0, 1],
   [1, 2, 1],
   [0, 1, 2, 1],
   [1, 2, 0, 1],
   [0, 1, 2, 0, 1],
   [2, 1, 0],
   [1, 0, 1, 2, 1, 0],
   [2, 0, 1, 0],
   [1, 0, 1, 2, 0, 1, 0],
   [1, 2, 1, 0],
   [0, 1, 2, 1, 0],
   [1, 2, 0, 1, 0],
   [0, 1, 2, 0, 1, 0]]

@[expose] def tabA : List (Fin 6 × Fin 6 × Fin 6) :=
  [(0, 2, 4),
   (0, 2, 5),
   (0, 3, 4),
   (0, 3, 5),
   (0, 4, 2),
   (0, 4, 3),
   (0, 5, 2),
   (0, 5, 3),
   (1, 2, 4),
   (1, 2, 5),
   (1, 3, 4),
   (1, 3, 5),
   (1, 4, 2),
   (1, 4, 3),
   (1, 5, 2),
   (1, 5, 3),
   (2, 0, 4),
   (2, 0, 5),
   (2, 1, 4),
   (2, 1, 5),
   (2, 4, 0),
   (2, 4, 1),
   (2, 5, 0),
   (2, 5, 1),
   (3, 0, 4),
   (3, 0, 5),
   (3, 1, 4),
   (3, 1, 5),
   (3, 4, 0),
   (3, 4, 1),
   (3, 5, 0),
   (3, 5, 1),
   (4, 0, 2),
   (4, 0, 3),
   (4, 1, 2),
   (4, 1, 3),
   (4, 2, 0),
   (4, 2, 1),
   (4, 3, 0),
   (4, 3, 1),
   (5, 0, 2),
   (5, 0, 3),
   (5, 1, 2),
   (5, 1, 3),
   (5, 2, 0),
   (5, 2, 1),
   (5, 3, 0),
   (5, 3, 1)]

@[expose] def wordsE : List (List (Fin 3)) :=
  [[],
   [1, 0, 1],
   [0],
   [1, 0, 1, 0],
   [1],
   [0, 1],
   [1, 0],
   [0, 1, 0]]

@[expose] def tabE : List (Fin 4 × Fin 4) :=
  [(0, 2),
   (0, 3),
   (1, 2),
   (1, 3),
   (2, 0),
   (2, 1),
   (3, 0),
   (3, 1)]

@[expose] def pA (m : Fin 48) : Perm (Fin 11) := wordP (wordsA.getD m [])

@[expose] def iA (m : Fin 48) : Fin 6 × Fin 6 × Fin 6 := tabA.getD m (0, 0, 0)

@[expose] def pE (m : Fin 8) : Perm (Fin 11) := wordP (wordsE.getD m [])

@[expose] def iE (m : Fin 8) : Fin 4 × Fin 4 := tabE.getD m (0, 0)

set_option maxRecDepth 100000 in
theorem sign_pA : ∀ m : Fin 48, sign (pA m) = 1 := by decide

set_option maxRecDepth 100000 in
theorem pA_conj : ∀ m : Fin 48,
    pA m * x1p * (pA m)⁻¹ = e6p (iA m).1 ∧ pA m * x2p * (pA m)⁻¹ = e6p (iA m).2.1 ∧
      pA m * x3p * (pA m)⁻¹ = e6p (iA m).2.2 := by decide

set_option maxRecDepth 100000 in
theorem iA_injective : Function.Injective iA := by decide

set_option maxRecDepth 100000 in
theorem iA_surjective : ∀ i j k : Fin 6, i.val / 2 ≠ j.val / 2 → i.val / 2 ≠ k.val / 2 →
    j.val / 2 ≠ k.val / 2 → ∃ m, iA m = (i, j, k) := by decide

theorem sign_pE : ∀ m : Fin 8, sign (pE m) = 1 := by decide

theorem pE_conj : ∀ m : Fin 8,
    pE m * x1p * (pE m)⁻¹ = e4p (iE m).1 ∧ pE m * x2p * (pE m)⁻¹ = e4p (iE m).2 := by decide

theorem iE_injective : Function.Injective iE := by decide

theorem iE_surjective : ∀ i j : Fin 4, i.val / 2 ≠ j.val / 2 → ∃ m, iE m = (i, j) := by decide

end CFSG.Sporadic.Recognition.LyonsSims
