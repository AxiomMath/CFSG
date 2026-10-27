module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthCoord

public section

namespace CFSG.StandardType

namespace EnnolaFork

open Multiplicative NbrFrameOne

variable {p k : ℕ}

theorem swapAut_braid {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swapAut a b * swapAut b c * swapAut a b : MulAut (Multiplicative (Fin k → ZMod p))) =
      swapAut b c * swapAut a b * swapAut b c := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f]
  simp only [MulAut.mul_apply, swapAut_apply]
  congr 1
  funext l
  simp only [Function.comp_apply]
  by_cases hla : l = a
  · subst hla
    simp [Equiv.swap_apply_def, hab, hac, Ne.symm hbc, Ne.symm hac]
  · by_cases hlb : l = b
    · subst hlb
      simp [Equiv.swap_apply_def, hab, hac, Ne.symm hbc, Ne.symm hac]
    · by_cases hlc : l = c
      · subst hlc
        simp [Equiv.swap_apply_def, hab, hac, Ne.symm hbc, Ne.symm hac]
      · simp [Equiv.swap_apply_def, hla, hlb, hlc]

theorem swapAut_comm_of_disjoint {a b c d : Fin k} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    (swapAut a b * swapAut c d : MulAut (Multiplicative (Fin k → ZMod p))) =
      swapAut c d * swapAut a b := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f]
  simp only [MulAut.mul_apply, swapAut_apply]
  congr 1
  funext l
  simp only [Function.comp_apply]
  by_cases hla : l = a
  · subst hla
    simp [Equiv.swap_apply_def, hac, had, hbc, hbd]
  · by_cases hlb : l = b
    · subst hlb
      simp [Equiv.swap_apply_def, hac, had, hbc, hbd]
    · by_cases hlc : l = c
      · subst hlc
        simp [Equiv.swap_apply_def, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
      · by_cases hld : l = d
        · subst hld
          simp [Equiv.swap_apply_def, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
        · simp [Equiv.swap_apply_def, hla, hlb, hlc, hld]

end EnnolaFork

end CFSG.StandardType

end
