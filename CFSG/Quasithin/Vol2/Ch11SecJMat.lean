module

public import CFSG.Quasithin.Background.G2SL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open Matrix CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open scoped MatrixGroups

variable {F : Type*} [Field F]

@[expose] def p12 : W3 F →* Wm F where
  toFun w := Multiplicative.ofAdd ![Multiplicative.toAdd w 1, Multiplicative.toAdd w 2]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp

theorem toAdd_p12 (w : W3 F) :
    Multiplicative.toAdd (p12 w) = ![Multiplicative.toAdd w 1, Multiplicative.toAdd w 2] := rfl

@[expose] def blk22 (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![A 1 1, A 1 2; A 2 1, A 2 2]

theorem blk22_mul {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) (B : SL(3, F)) :
    blk22 (A * B).1 = blk22 A.1 * blk22 B.1 := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk22, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, h1, h2]

theorem entry00_mul (A : SL(3, F)) {B : SL(3, F)} (hB : B ∈ Pt (vE F 0)) :
    (A * B).1 0 0 = A.1 0 0 * B.1 0 0 := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hB
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

theorem entry00_mul_det_blk22 {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) :
    A.1 0 0 * (blk22 A.1).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hA
  have hd := A.2
  rw [Matrix.det_fin_three, h1, h2] at hd
  rw [blk22, Matrix.det_fin_two_of]
  linear_combination hd

@[expose] def Pt1 (F : Type*) [Field F] : Subgroup SL(3, F) where
  carrier := {A | A ∈ Pt (vE F 0) ∧ A.1 0 0 = 1}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro A B ⟨hA, hA1⟩ ⟨hB, hB1⟩
    exact ⟨Subgroup.mul_mem _ hA hB, by rw [entry00_mul A hB, hA1, hB1, one_mul]⟩
  inv_mem' := by
    rintro A ⟨hA, hA1⟩
    refine ⟨Subgroup.inv_mem _ hA, ?_⟩
    have h := entry00_mul A⁻¹ hA
    rw [inv_mul_cancel, hA1, mul_one] at h
    simpa using h.symm

theorem det_blk22_of_mem_Pt1 {A : SL(3, F)} (hA : A ∈ Pt1 F) : (blk22 A.1).det = 1 := by
  have h := entry00_mul_det_blk22 hA.1
  rwa [hA.2, one_mul] at h

@[expose] noncomputable def blkHom : ↥(Pt1 F) →* SL(2, F) where
  toFun A := ⟨blk22 A.1.1, det_blk22_of_mem_Pt1 A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk22]
  map_mul' A B := Subtype.ext (blk22_mul A.2.1 B.1)

theorem p12_natAct3 {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) (w : W3 F) :
    Multiplicative.toAdd (p12 (natAct3 A w)) =
      blk22 A.1 *ᵥ Multiplicative.toAdd (p12 w) := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hA
  rw [toAdd_p12, toAdd_p12, natAct3_apply, toAdd_ofAdd]
  ext i
  fin_cases i <;>
    simp [blk22, smul_coord, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1, h2]

theorem mul_qhom [CharP F 2] {A : SL(3, F)} (hA : A ∈ Pt1 F) (q : Wm F) :
    A * qhom q = qhom (Multiplicative.ofAdd (blk22 A.1 *ᵥ Multiplicative.toAdd q)) * A := by
  obtain ⟨⟨h1, h2⟩, h0⟩ := And.imp_left mem_Pt_e0.1 hA
  have hdet := det_blk22_of_mem_Pt1 hA
  rw [blk22, Matrix.det_fin_two_of] at hdet
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, qhom_apply, tq_coe, Matrix.mul_apply,
      Fin.sum_univ_three, blk22, dotProduct, Fin.sum_univ_two, h0, h1, h2]
  · linear_combination (-(Multiplicative.toAdd q 1)) * hdet +
      (-(A.1 1 1 * A.1 2 1 * Multiplicative.toAdd q 0) -
        Multiplicative.toAdd q 1 * A.1 2 1 * A.1 1 2) * h2F
  · linear_combination (-(Multiplicative.toAdd q 0)) * hdet +
      (-(A.1 1 2 * A.1 2 2 * Multiplicative.toAdd q 1) -
        Multiplicative.toAdd q 0 * A.1 1 2 * A.1 2 1) * h2F

@[expose] noncomputable def dg (c : F) (hc : c ≠ 0) : SL(3, F) :=
  ⟨!![(c ^ 2)⁻¹, 0, 0; 0, c, 0; 0, 0, c], by
    simp [Matrix.det_fin_three]
    field_simp⟩

theorem dg_coe (c : F) (hc : c ≠ 0) :
    ((dg c hc : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![(c ^ 2)⁻¹, 0, 0; 0, c, 0; 0, 0, c] :=
  rfl

theorem dg_mem_Pt (c : F) (hc : c ≠ 0) : dg c hc ∈ Pt (vE F 0) := by
  rw [mem_Pt_e0]
  simp [dg_coe]

theorem p12_natAct3_dg (c : F) (hc : c ≠ 0) (w : W3 F) :
    Multiplicative.toAdd (p12 (natAct3 (dg c hc) w)) = c • Multiplicative.toAdd (p12 w) := by
  rw [toAdd_p12, toAdd_p12, natAct3_apply, toAdd_ofAdd]
  ext i
  fin_cases i <;> simp [smul_coord, dg_coe]

theorem dg_mul_qhom (c : F) (hc : c ≠ 0) (q : Wm F) :
    dg c hc * qhom q = qhom (Multiplicative.ofAdd ((c ^ 3)⁻¹ • Multiplicative.toAdd q)) *
      dg c hc := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, qhom_apply, tq_coe, dg_coe, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp

theorem dg_comm_mem_Qv (c : F) (hc : c ≠ 0) {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) :
    dg c hc * A * (dg c hc)⁻¹ * A⁻¹ ∈ Qv (vE F 0) := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hA
  have hdet := entry00_mul_det_blk22 hA
  rw [blk22, Matrix.det_fin_two_of] at hdet
  have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hkey : dg c hc * A =
      tq (((c ^ 3)⁻¹ - 1) * A.1 0 0 * (A.1 0 1 * A.1 2 2 - A.1 0 2 * A.1 2 1))
        (((c ^ 3)⁻¹ - 1) * A.1 0 0 * (A.1 0 2 * A.1 1 1 - A.1 0 1 * A.1 1 2)) * A *
        dg c hc := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, tq_coe, dg_coe, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_three, h1, h2]
    · ring
    · linear_combination (-(c * ((c ^ 3)⁻¹ - 1) * A.1 0 1)) * hdet +
        (-(c⁻¹ ^ 2 * A.1 0 1)) * hci
    · linear_combination (-(c * ((c ^ 3)⁻¹ - 1) * A.1 0 2)) * hdet +
        (-(c⁻¹ ^ 2 * A.1 0 2)) * hci
    all_goals ring
  have h3 : dg c hc * A * (dg c hc)⁻¹ * A⁻¹ =
      tq (((c ^ 3)⁻¹ - 1) * A.1 0 0 * (A.1 0 1 * A.1 2 2 - A.1 0 2 * A.1 2 1))
        (((c ^ 3)⁻¹ - 1) * A.1 0 0 * (A.1 0 2 * A.1 1 1 - A.1 0 1 * A.1 1 2)) := by
    rw [hkey]
    group
  rw [h3]
  exact tq_mem_Qv _ _

end CFSG.Quasithin.Vol2.Ch11.SecJ
