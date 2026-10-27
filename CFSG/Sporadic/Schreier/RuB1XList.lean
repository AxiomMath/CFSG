module

public import CFSG.Sporadic.Schreier.RuB1Objects
public import Certificates.Data.GMS78RuB1Check

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native RuB1

@[expose] def ruXElt (j : ℕ) : Equiv.Perm (Fin 4060) :=
  ruC0 ^ (j / 7) * ruEElt (j % 7) * ruC0⁻¹ ^ (j / 7)

theorem rep_xArr (j : ℕ) :
    Rep 4060 (xArr j) (ruXElt j) :=
  rep_compA (rep_compA (rep_powA rep_ruC0 _) (rep_ruEElt (Nat.mod_lt j (by norm_num))))
    (rep_powA (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1) _)

theorem xList_getElem {j : ℕ} (hj : j < 35) : xList[j]! = xArr j := by
  rw [xList, getElem!_ofFn' _ hj]

theorem rep_xList {j : ℕ}
    (hj : j < 35) : Rep 4060 xList[j]! (ruXElt j) := by
  rw [xList_getElem hj]
  exact rep_xArr j

theorem ruXElt_eq_conj (j : ℕ) :
    ruXElt j = ruC0 ^ (j / 7) * ruEElt (j % 7) * (ruC0 ^ (j / 7))⁻¹ := by
  rw [ruXElt, inv_pow]

theorem ruXElt_of_lt {j : ℕ} (hj : j < 7) : ruXElt j = ruEElt j := by
  rw [ruXElt, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, pow_zero, pow_zero, one_mul, mul_one]

theorem ruXElt_mem (j : ℕ) :
    ruXElt j ∈ ruXN :=
  Subgroup.subset_closure ⟨_, ruC.pow_mem ruC0_memC _, _,
    mem_ruESub.2 (Or.inr ⟨_, Nat.mod_lt j (by norm_num), rfl⟩), ruXElt_eq_conj j⟩

end CFSG.Sporadic.RuSchreier
