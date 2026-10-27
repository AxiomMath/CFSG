module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27H

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27.SL3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem sq_eq_one_of_rhoOne [CharP F 2] {x : ↥(stabilizer (flagSpace 3 F 1))}
    (hx : rhoOne x = 1) : x ^ 2 = 1 := by
  obtain ⟨h10, h20⟩ := mem_stab_one_iff.mp x.2
  set m := ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hm
  have hb : blkOne m = 1 := congrArg Units.val hx
  have hent : ∀ i j : Fin 2, m i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => congrFun (congrFun hb i) j
  have e11 := hent 0 0
  have e12 := hent 0 1
  have e21 := hent 1 0
  have e22 := hent 1 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, one_apply_eq] at e11 e12 e21 e22
  simp only [one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e12 e21
  have e00 : m 0 0 = 1 := by
    have h := det_eq_blkOne (g := m) ⟨h10, h20⟩
    rw [hb, det_one, mul_one] at h
    exact h.symm.trans (x : SpecialLinearGroup (Fin 3) F).prop
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Subgroup.coe_pow, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one, sq, ← hm]
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h10, h20, e11, e12, e21, e22, e00,
      CharTwo.add_self_eq_zero]

theorem sq_eq_one_of_rhoTwo [CharP F 2] {x : ↥(stabilizer (flagSpace 3 F 2))}
    (hx : rhoTwo x = 1) : x ^ 2 = 1 := by
  obtain ⟨h20, h21⟩ := mem_stab_two_iff.mp x.2
  set m := ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hm
  have hb : blkTwo m = 1 := congrArg Units.val hx
  have hent : ∀ i j : Fin 2, m i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => congrFun (congrFun hb i) j
  have e00 := hent 0 0
  have e01 := hent 0 1
  have e10 := hent 1 0
  have e11 := hent 1 1
  simp only [Fin.castSucc_zero, Fin.castSucc_one, one_apply_eq] at e00 e01 e10 e11
  simp only [one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e01 e10
  have e22 : m 2 2 = 1 := by
    have h := det_eq_blkTwo (g := m) ⟨h20, h21⟩
    rw [hb, det_one, one_mul] at h
    exact h.symm.trans (x : SpecialLinearGroup (Fin 3) F).prop
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Subgroup.coe_pow, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one, sq, ← hm]
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h20, h21, e00, e01, e10, e11, e22,
      CharTwo.add_self_eq_zero]

@[expose] def embOne (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

@[expose] def embTwo (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem embOne_mul (A B : Matrix (Fin 2) (Fin 2) F) : embOne (A * B) = embOne A * embOne B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embOne, mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem embTwo_mul (A B : Matrix (Fin 2) (Fin 2) F) : embTwo (A * B) = embTwo A * embTwo B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embTwo, mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem det_embOne (A : Matrix (Fin 2) (Fin 2) F) : (embOne A).det = A.det := by
  rw [det_fin_three, det_fin_two]
  simp [embOne]

theorem det_embTwo (A : Matrix (Fin 2) (Fin 2) F) : (embTwo A).det = A.det := by
  rw [det_fin_three, det_fin_two]
  simp [embTwo]

@[expose] noncomputable def iotaOne :
    SpecialLinearGroup (Fin 2) F →* ↥(stabilizer (flagSpace 3 F 1)) where
  toFun A := ⟨⟨embOne (A : Matrix (Fin 2) (Fin 2) F), by rw [det_embOne]; exact A.prop⟩,
    mem_stab_one_iff.mpr ⟨by simp [embOne], by simp [embOne]⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by
    show embOne (1 : Matrix (Fin 2) (Fin 2) F) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embOne]))
  map_mul' A B := Subtype.ext (Subtype.ext (embOne_mul (A : Matrix (Fin 2) (Fin 2) F) B))

@[expose] noncomputable def iotaTwo :
    SpecialLinearGroup (Fin 2) F →* ↥(stabilizer (flagSpace 3 F 2)) where
  toFun A := ⟨⟨embTwo (A : Matrix (Fin 2) (Fin 2) F), by rw [det_embTwo]; exact A.prop⟩,
    mem_stab_two_iff.mpr ⟨by simp [embTwo], by simp [embTwo]⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by
    show embTwo (1 : Matrix (Fin 2) (Fin 2) F) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embTwo]))
  map_mul' A B := Subtype.ext (Subtype.ext (embTwo_mul (A : Matrix (Fin 2) (Fin 2) F) B))

theorem rhoOne_iotaOne (A : SpecialLinearGroup (Fin 2) F) :
    rhoOne (iotaOne A) = SpecialLinearGroup.toGL A := by
  apply Units.ext
  show blkOne (embOne (A : Matrix (Fin 2) (Fin 2) F)) = A
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rhoTwo_iotaTwo (A : SpecialLinearGroup (Fin 2) F) :
    rhoTwo (iotaTwo A) = SpecialLinearGroup.toGL A := by
  apply Units.ext
  show blkTwo (embTwo (A : Matrix (Fin 2) (Fin 2) F)) = A
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CFSG.Quasithin.H13.Ch4.T425C27.SL3
