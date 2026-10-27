module

public import CFSG.Quasithin.Recognition.M12AmalAutJData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.Quasithin.M12AmalAut.JMul

@[expose] def lane7 (x j : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 7 j)) 127

#kc_repo #kc_decls CFSG.Quasithin.M12AmalAut.JMul "CFSG/Quasithin/Recognition/data/m12amalautj_mul.txt" 34126 1183310130125454891

@[expose] noncomputable def mK (i j : Nat) : Nat :=
  Bool.rec 0 (Bool.rec 0 (lane7 (Nat.shiftRight mT (Nat.mul 896 i)) j) (Nat.blt j 128)) (Nat.blt i 128)

theorem telMulTab_eq : telMulTab =
    (List.range 128).map fun i => (List.range 128).map fun j => lane7 (Nat.shiftRight mT (Nat.mul 896 i)) j :=
  eq_of_beq (by decide +kernel)

theorem getD_mK (i j : Nat) : (telMulTab.getD i []).getD j 0 = mK i j := by
  rw [telMulTab_eq, mK]
  by_cases hi : i < 128
  · by_cases hj : j < 128
    · simp [hi, hj, List.getD_eq_getElem?_getD, Nat.blt_eq.mpr hi, Nat.blt_eq.mpr hj]
    · have hb : Nat.blt j 128 = false := by
        cases h : Nat.blt j 128
        · rfl
        · exact absurd (Nat.blt_eq.mp h) hj
      simp [hi, hj, hb, List.getD_eq_getElem?_getD, Nat.blt_eq.mpr hi]
  · have hb : Nat.blt i 128 = false := by
      cases h : Nat.blt i 128
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hi
    simp [hi, hb, List.getD_eq_getElem?_getD]

end CFSG.Quasithin.M12AmalAut.JMul
