module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointTorus

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem sMat_mul_self_u4 (x y c : K) :
    sMat h x y c * sMat h x y c = sMat h 0 0 (h.bar y * x + h.bar x * y) := by
  have := h.charP
  rw [sMat_mul, CharTwo.add_self_eq_zero x, CharTwo.add_self_eq_zero y,
    CharTwo.add_self_eq_zero c, zero_add]

theorem coe_levHom_of_eq {A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField} {t : h.fixedField}
    (hA : (A : Matrix (Fin 2) (Fin 2) h.fixedField) = !![1, t; 0, 1]) :
    (((levHom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = u4xbMat (t : K) := by
  rw [coe_levHom]
  ext i j
  rw [levMat_apply, u4xbMat_apply]
  simp only [slMat, hA, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Subfield.coe_subtype, Subfield.coe_one, Subfield.coe_zero]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [one_apply, ie1, ie2, if1, if2]

theorem levHom_mem_radQ2_of_eq {A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField}
    {t : h.fixedField} (hA : (A : Matrix (Fin 2) (Fin 2) h.fixedField) = !![1, t; 0, 1]) :
    levHom h A ∈ radQ2 h := by
  have ht : h.bar (t : K) = t := (h.mem_fixedField).mp t.2
  have he : levHom h A = u4xbElt h ht := hypSU_ext h (by rw [coe_levHom_of_eq h hA, coe_u4xbElt])
  rw [he]
  exact u4xbElt_mem_radQ2 h ht

theorem levHom_mul_mem_hypUnitriangular_iff (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField)
    {d : hypSU h 2 0} (hd : d ∈ u4PtTorus h) :
    levHom h A * d ∈ hypUnitriangular h 2 0 ↔
      d = 1 ∧ ∃ t : h.fixedField, (A : Matrix (Fin 2) (Fin 2) h.fixedField) = !![1, t; 0, 1] := by
  have := h.charP
  obtain ⟨q, hq, hq24⟩ := hd
  constructor
  · intro hu
    obtain ⟨hbt, hdiag⟩ := mem_hypUnitriangular.mp hu
    have hM : (((levHom h A * d : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
        levMat (slMat h A) * diagonal q := by
      rw [coe_mul_hypSU, coe_levHom, hq]
    have entry : ∀ i j, (((levHom h A * d : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) i j =
        levMat (slMat h A) i j * q j := fun i j => by rw [hM, mul_diagonal]
    have e11 := hdiag ie1
    have e33 := hdiag if1
    have e22 := hdiag ie2
    have e44 := hdiag if2
    have e42 : (((levHom h A * d : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) if2 ie2 = 0 :=
      hbt (by decide)
    rw [entry, levMat_apply] at e11 e33 e22 e44 e42
    simp [ie1, ie2, if1, if2] at e11 e33 e22 e44 e42
    have e11' : q ie1 = 1 := e11
    have e33' : q if1 = 1 := e33
    have e22' : slMat h A 0 0 * q ie2 = 1 := e22
    have e44' : slMat h A 1 1 * q ie2 = 1 := by rw [hq24]; exact e44
    have e42' : slMat h A 1 0 = 0 ∨ q ie2 = 0 := e42
    have hq2 : q ie2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e22'
      exact zero_ne_one e22'
    have hA10 : slMat h A 1 0 = 0 := e42'.resolve_right hq2
    have hdet : (slMat h A).det = 1 := by
      have e := RingHom.map_det h.fixedField.subtype (A : Matrix (Fin 2) (Fin 2) h.fixedField)
      rw [Matrix.SpecialLinearGroup.det_coe, map_one, RingHom.mapMatrix_apply] at e
      exact e.symm
    rw [det_fin_two, hA10, mul_zero, sub_zero] at hdet
    have h00 : slMat h A 0 0 = slMat h A 1 1 :=
      mul_right_cancel₀ hq2 (e22'.trans e44'.symm)
    have hsq : slMat h A 0 0 ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h00]; exact hdet
    have h1 : slMat h A 0 0 = 1 := by
      have := (CharTwo.sq_inj (R := K)).mp (hsq.trans (one_pow 2).symm)
      exact this
    have hq2' : q ie2 = 1 := by rw [h1, one_mul] at e22'; exact e22'
    refine ⟨?_, ⟨(A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1, ?_⟩⟩
    · apply hypSU_ext h
      rw [hq]
      have hq1 : q = fun _ => 1 := by
        funext i
        rcases ix_cases i with rfl | rfl | rfl | rfl
        · exact e11'
        · exact hq2'
        · exact e33'
        · rw [← hq24]; exact hq2'
      rw [hq1]
      exact diagonal_one
    · have h00F : (A : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 = 1 :=
        Subtype.ext (by simpa [slMat] using h1)
      have h1' : slMat h A 1 1 = 1 := h00 ▸ h1
      have h11F : (A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 = 1 :=
        Subtype.ext (by simpa [slMat] using h1')
      have h10F : (A : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 = 0 :=
        Subtype.ext (by simpa [slMat] using hA10)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00F, h11F, h10F]
  · rintro ⟨rfl, t, ht⟩
    have htb : h.bar (t : K) = t := (h.mem_fixedField).mp t.2
    have he : levHom h A = u4xbElt h htb :=
      hypSU_ext h (by rw [coe_levHom_of_eq h ht, coe_u4xbElt])
    rw [mul_one, he]
    exact u4xbElt_mem_hypUnitriangular h htb

end CFSG.Quasithin.F112R.St84

end
