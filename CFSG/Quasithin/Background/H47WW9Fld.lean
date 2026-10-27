module

public import CFSG.Quasithin.Background.HL3NineW9
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H47W

open CFSG.Fischer Matrix CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9

theorem herm_one_eq : herm 1 = Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem herm_two_eq : herm 2 = Matrix.of ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem herm_eight_eq : herm 8 = Matrix.of ![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem herm_sixteen_eq :
    herm 16 = Matrix.of ![![0, mk 0 1, 0], ![cj (mk 0 1), 0, 0], ![0, 0, 0]] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem om_add_cj : mk 0 1 + mk 0 1 * mk 0 1 = 1 := by rfl

theorem no_entry_identity (a b p q : F4) (h1 : a * (a * a) = 1) (h2 : b * (b * b) = 1)
    (h8 : p * (q * q) + a * (b * b) = 1)
    (h16 : a * mk 0 1 * (b * b) + p * (mk 0 1 * mk 0 1) * (q * q) = mk 0 1 * mk 0 1) : False := by
  set A : F4 := a * (b * b) with hA
  set B : F4 := p * (q * q) with hB
  set w : F4 := mk 0 1 * mk 0 1 with hw
  have hsum : mk 0 1 + w = 1 := om_add_cj
  have hAz : A * (mk 0 1 + w) = 0 := by
    have h2' : (2 : F4) = 0 := F4.two_eq_zero
    linear_combination (h16 : a * mk 0 1 * (b * b) + p * w * (q * q) = w) -
      w * h8 + (w * A) * h2'
  rw [hsum, mul_one] at hAz
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  have hA0 : A ≠ 0 := mul_ne_zero ha0 (mul_ne_zero hb0 hb0)
  exact hA0 hAz

theorem fld9_not_mem_img9 : fld9 ∉ img9 := by
  rintro ⟨g, hg⟩
  have hg' : rho9 (Matrix.SpecialLinearGroup.toGL g) = fld9 := hg
  set N : Matrix (Fin 3) (Fin 3) F4 :=
    ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) with hN
  have hact : ∀ m : Fin 512, act N m = fld m := by
    intro m
    apply toW9.injective
    rw [← rho9_toW9, ← fld9_toW9, hg']
  have hherm : ∀ m : Fin 512, N * herm m * (bar N)ᵀ = bar (herm m) := by
    intro m
    rw [← herm_act, hact, herm_fld]
  have e1 := congrFun (congrFun (hherm 1) 0) 0
  have e2 := congrFun (congrFun (hherm 2) 1) 1
  have e8 := congrFun (congrFun (hherm 8) 0) 1
  have e16 := congrFun (congrFun (hherm 16) 0) 1
  rw [herm_one_eq] at e1
  rw [herm_two_eq] at e2
  rw [herm_eight_eq] at e8
  rw [herm_sixteen_eq] at e16
  simp only [Matrix.mul_apply, Fin.sum_univ_three, bar, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.tail_cons, cj] at e1 e2 e8 e16
  exact no_entry_identity (N 0 0) (N 1 1) (N 0 1) (N 1 0) (by linear_combination e1)
    (by linear_combination e2) (by linear_combination e8) (by linear_combination e16)

end CFSG.Quasithin.H47W
