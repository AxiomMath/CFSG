module

public import CFSG.Quasithin.Vol2.Asc94.He42P427H1

public section

namespace CFSG.Quasithin.A94.He42P427H

open CFSG.Quasithin.A94.L52 Matrix

theorem Phi_comm_abar (p : Fin 9 → ZMod 2) : Phi p * abar = abar * Phi p := by
  apply Subtype.ext
  apply Subtype.ext
  show cm (Phi p) * cm abar = cm abar * cm (Phi p)
  rw [show cm (Phi p) = Xm (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) from
    by simp only [Phi, cm_Phi']]
  ext i j
  rw [cm_abar]
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.mul_apply, Fin.sum_univ_five] <;> ring

theorem cm_eq_Xm_of_comm (x : Hc) (hx : x * abar = abar * x) :
    cm x = Xm (prm x 0) (prm x 1) (prm x 2) (prm x 3) (prm x 4) (prm x 5) (prm x 6) (prm x 7)
      (prm x 8) := by
  have hm : cm x * cm abar = cm abar * cm x := by
    have h := congrArg cm hx
    exact h
  have c10 : cm x 1 0 = 0 := by rw [cm_col0]; simp
  have c20 : cm x 2 0 = 0 := by rw [cm_col0]; simp
  have c30 : cm x 3 0 = 0 := by rw [cm_col0]; simp
  have c40 : cm x 4 0 = 0 := by rw [cm_col0]; simp
  have c41 : cm x 4 1 = 0 := by rw [cm_row4]; simp
  have c42 : cm x 4 2 = 0 := by rw [cm_row4]; simp
  have c43 : cm x 4 3 = 0 := by rw [cm_row4]; simp
  have c44 : cm x 4 4 = 1 := by rw [cm_44]
  have c00 : cm x 0 0 = 1 := by rw [cm_00]
  have e14 := congrFun (congrFun hm 1) 4
  have e24 := congrFun (congrFun hm 2) 4
  have e34 := congrFun (congrFun hm 3) 4
  have e04 := congrFun (congrFun hm 0) 4
  have e02 := congrFun (congrFun hm 0) 2
  have e03 := congrFun (congrFun hm 0) 3
  have e01 := congrFun (congrFun hm 0) 1
  rw [cm_abar] at e14 e24 e34 e04 e02 e03 e01 hm
  simp only [Matrix.mul_apply, Fin.sum_univ_five] at e14 e24 e34 e04 e02 e03 e01
  simp only [c10, c20, c30, c40, c41, c42, c43, c44, c00] at e14 e24 e34 e04 e02 e03 e01
  simp at e14 e24 e34 e04 e02 e03 e01
  have x11 : cm x 1 1 = 1 := by linear_combination e14
  have x21 : cm x 2 1 = 0 := by linear_combination e24
  have x31 : cm x 3 1 = 0 := by linear_combination e34
  have x32 : cm x 3 2 = 0 := by linear_combination e02
  have x33 : cm x 3 3 = 1 := by linear_combination -e03
  have x34 : cm x 3 4 = cm x 0 1 := by linear_combination -e04
  clear hm e14 e24 e34 e04 e02 e03 e01
  have hup : (cm x).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [c10, c20, c30, c40, c41, c42, c43, x21, x31, x32]
  have hdet : (cm x).det = 1 := Matrix.SpecialLinearGroup.det_coe x.1
  rw [Matrix.det_of_isUpperTriangular hup, Fin.prod_univ_five, c00, x11, x33, c44] at hdet
  have x22 : cm x 2 2 = 1 := by simpa using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xm, prm, cm_col0 x, cm_row4 x, c00, c10, c20, c30, x11, x21, x22, x31, x32, x33, x34]

theorem eq_Phi_of_comm (x : Hc) (hx : x * abar = abar * x) : x = Phi (prm x) := by
  apply Subtype.ext
  apply Subtype.ext
  show cm x = Xm (prm x 0) (prm x 1) (prm x 2) (prm x 3) (prm x 4) (prm x 5) (prm x 6) (prm x 7)
    (prm x 8)
  exact cm_eq_Xm_of_comm x hx

end CFSG.Quasithin.A94.He42P427H
