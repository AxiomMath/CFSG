module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DGenInputs
public import CFSG.RankThree.Native.ONTripleMatSound

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def e27InitG (j : ℕ) : Array Mat45ˣ :=
  Array.ofFn (n := 9) fun i =>
    if i.val < 8 then (eM (e27NReg j i.val))⁻¹ * eM (e27KReg i.val) * eM (e27NReg j i.val)
    else eM 7

theorem e27InitG_getD (j : ℕ) {k : ℕ} (hk : k < 9) :
    (e27InitG j).getD k 1 = (if k < 8 then (eM (e27NReg j k))⁻¹ * eM (e27KReg k) *
      eM (e27NReg j k) else eM 7) := by
  rw [e27InitG, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hk, dite_true, Option.getD_some]

theorem e27InitG_getD_of_ge (j : ℕ) {k : ℕ} (hk : 9 ≤ k) : (e27InitG j).getD k 1 = 1 := by
  rw [e27InitG, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [show ¬ k < 9 by omega, dite_false, Option.getD_none]

theorem e27NReg_lt {j : ℕ} (hj : j < 2) {i : ℕ} (hi : i < 8) : e27NReg j i < 200 :=
  rL_lt j hj (i / 2) (by omega)

theorem e27KReg_lt (i : ℕ) : e27KReg i < 200 := by
  unfold e27KReg
  split
  · exact regs_lt.2.2.1
  · exact regs_lt.2.2.2.1

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
