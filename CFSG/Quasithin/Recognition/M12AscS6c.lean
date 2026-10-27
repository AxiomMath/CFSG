module

public import CFSG.Quasithin.Recognition.M12AscS6b
public import CFSG.Quasithin.Recognition.M12AscS6

public section

namespace CFSG.Quasithin

open Equiv

@[expose] def tA1 : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5
@[expose] def tA2 : Perm (Fin 6) := swap 0 2 * swap 1 4 * swap 3 5
@[expose] def tA3 : Perm (Fin 6) := swap 0 1 * swap 2 5 * swap 3 4
@[expose] def tA4 : Perm (Fin 6) := swap 0 5 * swap 1 4 * swap 2 3
@[expose] def tA5 : Perm (Fin 6) := swap 0 1 * swap 2 4 * swap 3 5
@[expose] def tD2 : Perm (Fin 6) := swap 0 3 * swap 1 5 * swap 2 4
@[expose] def tD4 : Perm (Fin 6) := swap 0 4 * swap 1 5 * swap 2 3
@[expose] def tE2 : Perm (Fin 6) := swap 0 4 * swap 1 2 * swap 3 5
@[expose] def tE4 : Perm (Fin 6) := swap 0 4 * swap 1 5 * swap 2 3
@[expose] def tF2 : Perm (Fin 6) := swap 0 5 * swap 1 3 * swap 2 4
@[expose] def tF4 : Perm (Fin 6) := swap 0 5 * swap 1 4 * swap 2 3

@[expose] def candTuple (t2 t4 : Perm (Fin 6)) : Fin 5 → Perm (Fin 6) := ![tA1, t2, tA3, t4, tA5]

@[expose] def TA : Fin 5 → Perm (Fin 6) := candTuple tA2 tA4
@[expose] def TD : Fin 5 → Perm (Fin 6) := candTuple tD2 tD4
@[expose] def TE : Fin 5 → Perm (Fin 6) := candTuple tE2 tE4
@[expose] def TF : Fin 5 → Perm (Fin 6) := candTuple tF2 tF4

theorem tA1_eq_ps : tA1 = ps := by decide +kernel

theorem enum_tau : ∀ t4 : Perm (Fin 6),
    (t4 * t4 = 1 ∧ (tA3 * t4) ^ 3 = 1 ∧ (t4 * tA5) ^ 3 = 1 ∧ (tA1 * t4) ^ 2 = 1 ∧
      t4 * (tA3 * tA5) * t4 = pa * pb) →
    ∀ t2 : Perm (Fin 6),
      (t2 * t2 = 1 ∧ (tA1 * t2) ^ 3 = 1 ∧ (t2 * tA3) ^ 3 = 1 ∧ (t2 * t4) ^ 2 = 1 ∧
        (t2 * tA5) ^ 2 = 1) →
      (t2 = tA2 ∧ t4 = tA4) ∨ (t2 = tD2 ∧ t4 = tD4) ∨ (t2 = tE2 ∧ t4 = tE4) ∨
        (t2 = tF2 ∧ t4 = tF4) := by
  decide +kernel

theorem word_E2 : evalWord swapGen [0, 1, 0, 3, 2, 1, 0, 4, 3] = tE2 := by decide +kernel
theorem word_F2 : evalWord swapGen [0, 1, 2, 1, 0, 3, 2, 1, 4, 3, 2, 1, 0] = tF2 := by
  decide +kernel

theorem alpha2_E : evalWord TE [0, 1, 0, 3, 2, 1, 0, 4, 3] ≠ pa * swap 1 2 * pa := by
  decide +kernel

theorem alpha2_F : evalWord TF [0, 1, 2, 1, 0, 3, 2, 1, 4, 3, 2, 1, 0] ≠ pa * swap 1 2 * pa := by
  decide +kernel

theorem TD_conj_TA : ∀ i : Fin 5, pa * TD i * pa = TA i := by decide +kernel

theorem TA_cox : (∀ i : Fin 5, TA i * TA i = 1) ∧
    ∀ i j : Fin 5, i.val < j.val → (TA i * TA j) ^ coxExp i j = 1 := by decide +kernel

theorem tA3_mul_tA5 : tA3 * tA5 = pa := by decide +kernel
theorem tA5_eq : swap 0 1 * pcp = tA5 := by decide +kernel
theorem tA3_eq : pa * (swap 0 1 * pcp) = tA3 := by decide +kernel
theorem pcp_eq : pcp = swap 3 4 * pa * swap 3 4 := by decide +kernel

end CFSG.Quasithin
