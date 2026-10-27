module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord

public section

namespace CFSG.StandardType

namespace EnnolaFork

open Multiplicative NbrFrameOne

variable {p k : ℕ}

@[expose] def antiSwapAut (i j : Fin k) : MulAut (Multiplicative (Fin k → ZMod p)) :=
  negAut i * negAut j * swapAut i j

theorem antiSwapAut_apply {i j : Fin k} (hij : i ≠ j) (t : Fin k → ZMod p) :
    antiSwapAut i j (ofAdd t) =
      ofAdd (fun l => if l = i then -t j else if l = j then -t i else t l) := by
  rw [antiSwapAut, MulAut.mul_apply, MulAut.mul_apply, swapAut_apply, negAut_apply, negAut_apply]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl
    simp [Function.update_of_ne hij]
  · by_cases hl2 : l = j
    · subst hl2
      simp [hl]
    · simp [hl, hl2, Equiv.swap_apply_of_ne_of_ne hl hl2]

theorem antiSwapAut_sq {i j : Fin k} (hij : i ≠ j) :
    (antiSwapAut i j : MulAut (Multiplicative (Fin k → ZMod p))) ^ 2 = 1 := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f, sq, MulAut.mul_apply, antiSwapAut_apply hij, antiSwapAut_apply hij]
  simp only [MulAut.one_apply]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl
    simp [Ne.symm hij]
  · by_cases hl2 : l = j
    · subst hl2
      simp [hl]
    · simp [hl, hl2]

@[expose] def forkAut (a b c d : Fin k) : Fin 4 → MulAut (Multiplicative (Fin k → ZMod p)) :=
  ![swapAut b c, swapAut a b, swapAut c d, antiSwapAut c d]

theorem forkAut_zero (a b c d : Fin k) :
    (forkAut a b c d 0 : MulAut (Multiplicative (Fin k → ZMod p))) = swapAut b c := rfl

theorem forkAut_one (a b c d : Fin k) :
    (forkAut a b c d 1 : MulAut (Multiplicative (Fin k → ZMod p))) = swapAut a b := rfl

theorem forkAut_two (a b c d : Fin k) :
    (forkAut a b c d 2 : MulAut (Multiplicative (Fin k → ZMod p))) = swapAut c d := rfl

theorem forkAut_three (a b c d : Fin k) :
    (forkAut a b c d 3 : MulAut (Multiplicative (Fin k → ZMod p))) = antiSwapAut c d := rfl

end EnnolaFork

end CFSG.StandardType

end
