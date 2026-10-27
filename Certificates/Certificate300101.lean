module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.Certificates.Kernel.F7Max.Sound
import Certificates.Kernel.F7Max.Checks

public section

namespace Certificates

abbrev uHat7S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)) :=
  Subgroup.closure {g | (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 5; 2, 1] ∨
    (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 0; 0, 6]}

end Certificates

public section

namespace Certificates

open CFSG.KC.F7Max

private theorem matC_477 : matC 477 = !![1, 5; 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem matC_2059 : matC 2059 = !![1, 0; 0, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem uHat7S_eq_U0 : Certificates.uHat7S = U0 := by
  rw [Certificates.uHat7S, U0]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  have hz : (eltC 477 : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 5; 2, 1] := by
    rw [eltC_val (by decide +kernel), matC_477]
  have hs : (eltC 2059 : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![1, 0; 0, 6] := by
    rw [eltC_val (by decide +kernel), matC_2059]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext (h.trans hz.symm))
    · exact Or.inr (Units.ext (h.trans hs.symm))
  · rintro (rfl | rfl)
    · exact Or.inl hz
    · exact Or.inr hs

theorem certificate300101 : ∀ H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)), uHat7S ≤ H →
    H = uHat7S ∨ H = ⊤ :=
  by
    rw [uHat7S_eq_U0]
    exact maximal_of_checks coverOK_eq genOK_399 genOK_742 genOK_1134

end Certificates
