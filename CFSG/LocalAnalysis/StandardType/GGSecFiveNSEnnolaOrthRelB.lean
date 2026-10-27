module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthCoord

public section

namespace CFSG.StandardType

namespace EnnolaFork

open Multiplicative NbrFrameOne

variable {p k : ℕ}

theorem swapAut_antiSwapAut_braid {b c d : Fin k} (hbc : b ≠ c) (hcd : c ≠ d) (hbd : b ≠ d) :
    (swapAut b c * antiSwapAut c d * swapAut b c : MulAut (Multiplicative (Fin k → ZMod p))) =
      antiSwapAut c d * swapAut b c * antiSwapAut c d := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f]
  simp only [MulAut.mul_apply, swapAut_apply, antiSwapAut_apply hcd]
  rw [ofAdd.injective.eq_iff]
  funext l
  by_cases hb : l = b
  · simp [hb, hbc, hbd, hcd.symm, hbd.symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne]
  · by_cases hc : l = c
    · simp [hc, hbc, hbd, hcd.symm, hbd.symm, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · by_cases hd : l = d
      · simp [hd, hbc, hbd, hcd.symm, hbd.symm, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne]
      · simp [hb, hc, hd, hcd.symm, hbd.symm, Equiv.swap_apply_of_ne_of_ne]

theorem swapAut_antiSwapAut_comm_of_disjoint {a b c d : Fin k} (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (swapAut a b * antiSwapAut c d : MulAut (Multiplicative (Fin k → ZMod p))) =
      antiSwapAut c d * swapAut a b := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f]
  simp only [MulAut.mul_apply, swapAut_apply, antiSwapAut_apply hcd]
  rw [ofAdd.injective.eq_iff]
  funext l
  by_cases ha : l = a
  · simp [ha, hac, had, hbc, hbd, Equiv.swap_apply_left]
  · by_cases hb : l = b
    · simp [hb, hac, had, hbc, hbd, Equiv.swap_apply_right]
    · by_cases hc : l = c
      · simp [hc, hac.symm, had.symm, hbc.symm, hbd.symm, Equiv.swap_apply_of_ne_of_ne]
      · by_cases hd : l = d
        · simp [hd, hac.symm, had.symm, hbc.symm, hbd.symm, Equiv.swap_apply_of_ne_of_ne]
        · simp [ha, hb, hc, hd, Equiv.swap_apply_of_ne_of_ne]

theorem swapAut_antiSwapAut_comm {c d : Fin k} (hcd : c ≠ d) :
    (swapAut c d * antiSwapAut c d : MulAut (Multiplicative (Fin k → ZMod p))) =
      antiSwapAut c d * swapAut c d := by
  refine MulEquiv.ext fun f => ?_
  rw [← ofAdd_toAdd f]
  simp only [MulAut.mul_apply, swapAut_apply, antiSwapAut_apply hcd]
  rw [ofAdd.injective.eq_iff]
  funext l
  by_cases hc : l = c
  · simp [hc, hcd.symm, Equiv.swap_apply_left, Equiv.swap_apply_right]
  · by_cases hd : l = d
    · simp [hd, hcd.symm, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · simp [hc, hd, Equiv.swap_apply_of_ne_of_ne]

end EnnolaFork

end CFSG.StandardType

end
