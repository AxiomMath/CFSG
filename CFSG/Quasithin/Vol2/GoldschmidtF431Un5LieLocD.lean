module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocC
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Perfect

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.EvenBN.U4 (diagSL2 coe_diagSL2 mem_commutator_range_of_SL2
  conj_mem_commutator_self exists_fixed_unit_sq_ne_one)
open CFSG.LieType.Universal.Spin (upperSL2 coe_upperSL2 upperSL2_add)
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} [CharP K 2]

theorem exists_sqrt_F (c : h.fixedField) : ∃ r : h.fixedField, r * r = c := by
  have := h.finite
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq h.fixedField 2) c
  exact ⟨r, hr.symm⟩

theorem exists_ne_zero_one_F (hf : 2 ≤ f) : ∃ y : h.fixedField, y ≠ 0 ∧ y ≠ 1 := by
  obtain ⟨t, htF, ht⟩ := exists_fixed_unit_sq_ne_one h hf
  refine ⟨⟨(t : K), h.mem_fixedField.2 htF⟩, fun e => t.ne_zero (congrArg Subtype.val e),
    fun e => ht ?_⟩
  have : (t : K) = 1 := congrArg Subtype.val e
  rw [this, one_pow]

@[expose] def Kt (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) := Vt h ⊔ L0 h

theorem levHom_mem_Kt (A : SpecialLinearGroup (Fin 2) h.fixedField) : levHom h A ∈ Kt h :=
  Subgroup.mem_sup_right ⟨A, rfl⟩

theorem Vt_le_Kt : Vt h ≤ Kt h := le_sup_left

theorem L0_le_Kt : L0 h ≤ Kt h := le_sup_right

theorem commutator_mem_comm (A : SpecialLinearGroup (Fin 2) h.fixedField) {v : hypSU h 2 1}
    (hv : v ∈ Vt h) : ⁅levHom h A, v⁆ ∈ ⁅Kt h, Kt h⁆ :=
  Subgroup.commutator_mem_commutator (levHom_mem_Kt A) (Vt_le_Kt hv)

theorem Kt_commutator_le : ⁅Kt h, Kt h⁆ ≤ Kt h := commutator_le_self _

theorem L0_le_comm (hf : 2 ≤ f) : L0 h ≤ ⁅Kt h, Kt h⁆ := by
  obtain ⟨y, hy0, hy1⟩ := exists_ne_zero_one_F (h := h) hf
  have hl : ((Units.mk0 y hy0 : h.fixedFieldˣ) : h.fixedField) ^ 2 ≠ 1 := by
    intro e
    have e' : (y - 1) * (y - 1) = 0 := by
      have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
      simp only [Units.val_mk0] at e
      linear_combination e + (1 - y) * h2
    exact hy1 (sub_eq_zero.1 (mul_self_eq_zero.1 e'))
  rintro _ ⟨A, rfl⟩
  have := mem_commutator_range_of_SL2 (levHom h) hl A
  exact Subgroup.commutator_mono L0_le_Kt L0_le_Kt this

theorem comm_diag_vE11 (l : h.fixedFieldˣ) (c : h.fixedField) :
    ⁅levHom h (diagSL2 l), vE11 c⁆ = vE11 (((l : h.fixedField) ^ 2 + 1) * c) := by
  have hc := commutator_levHom_Vsub (diagSL2 l) (Vt_le_Vsub h (vE11_mem_Vt c))
  refine Yof_injOn h hc.1 (Vt_le_Vsub h (vE11_mem_Vt _)) ?_
  rw [hc.2, Yof_vE11, Yof_vE11]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slM_apply, coe_diagSL2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[expose] def wSL (h : UnitaryFieldData 2 f K) : SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

theorem slM_wSL : slM (wSL h) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem slM_upperSL2 (s : h.fixedField) : slM (upperSL2 s) = !![1, (s : K); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slM_apply, coe_upperSL2]

theorem vE11_mem_comm_ne (c : h.fixedField) (hc : c ≠ 1) : vE11 c ∈ ⁅Kt h, Kt h⁆ := by
  have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
  obtain ⟨s, hs⟩ := exists_sqrt_F (h := h) (c + 1)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hc (by linear_combination -hs - h2)
  have hcs : ((Units.mk0 s hs0 : h.fixedFieldˣ) : h.fixedField) ^ 2 + 1 = c := by
    simp only [Units.val_mk0]
    linear_combination hs + h2
  have := commutator_mem_comm (diagSL2 (Units.mk0 s hs0)) (vE11_mem_Vt (1 : h.fixedField))
  rwa [comm_diag_vE11, hcs, mul_one] at this

theorem vE11_mem_comm (hf : 2 ≤ f) (c : h.fixedField) : vE11 c ∈ ⁅Kt h, Kt h⁆ := by
  have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
  by_cases hc : c = 1
  · obtain ⟨y, hy0, hy1⟩ := exists_ne_zero_one_F (h := h) hf
    have hy : (1 : h.fixedField) = y + (y + 1) := by linear_combination (-y) * h2
    have hy' : y + 1 ≠ 1 := fun e => hy0 (by linear_combination e)
    rw [hc, hy, vE11_add]
    exact mul_mem (vE11_mem_comm_ne y hy1) (vE11_mem_comm_ne _ hy')
  · exact vE11_mem_comm_ne c hc

theorem vE22_mem_comm (hf : 2 ≤ f) (c : h.fixedField) : vE22 c ∈ ⁅Kt h, Kt h⁆ := by
  have hv := Vt_le_Vsub h (vE11_mem_Vt c)
  obtain ⟨hm, hY⟩ := Yof_levHom_conj (wSL h) hv
  have e : vE22 c = levHom h (wSL h) * vE11 c * (levHom h (wSL h))⁻¹ := by
    refine Yof_injOn h (Vt_le_Vsub h (vE22_mem_Vt c)) hm ?_
    rw [hY, slM_wSL, Yof_vE11, Yof_vE22]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have := conj_mem_commutator_self (H := Kt h) (x := (levHom h (wSL h))⁻¹)
    (inv_mem (levHom_mem_Kt (wSL h))) (vE11_mem_comm hf c)
  rwa [inv_inv, ← e] at this

theorem comm_upper_vE22 (s : h.fixedField) :
    ⁅levHom h (upperSL2 s), vE22 1⁆ = vE11 (s * s) * vJ s := by
  have hc := commutator_levHom_Vsub (upperSL2 s) (Vt_le_Vsub h (vE22_mem_Vt (1 : h.fixedField)))
  refine Yof_injOn h hc.1 (mul_mem (Vt_le_Vsub h (vE11_mem_Vt _)) (Vt_le_Vsub h (vJ_mem_Vt _))) ?_
  rw [hc.2, Yof_mul_Vsub (Vt_le_Vsub h (vE11_mem_Vt _)) (Vt_le_Vsub h (vJ_mem_Vt _)),
    slM_upperSL2, Yof_vE22, Yof_vE11, Yof_vJ]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul_transpose]
  linear_combination h2

theorem vJ_mem_comm (hf : 2 ≤ f) (s : h.fixedField) : vJ s ∈ ⁅Kt h, Kt h⁆ := by
  have h1 := commutator_mem_comm (upperSL2 s) (vE22_mem_Vt (1 : h.fixedField))
  rw [comm_upper_vE22] at h1
  have h3 := mul_mem (inv_mem (vE11_mem_comm hf (s * s))) h1
  rwa [inv_mul_cancel_left] at h3

theorem Vt_le_comm (hf : 2 ≤ f) : Vt h ≤ ⁅Kt h, Kt h⁆ := by
  intro g hg
  obtain ⟨a, d, b, rfl⟩ := mem_Vt_iff.1 hg
  exact mul_mem (mul_mem (vE11_mem_comm hf a) (vE22_mem_comm hf d)) (vJ_mem_comm hf b)

theorem Kt_perfect (hf : 2 ≤ f) : ⁅Kt h, Kt h⁆ = Kt h :=
  le_antisymm Kt_commutator_le (sup_le (Vt_le_comm hf) (L0_le_comm hf))

end CFSG.Quasithin.H13.F431.Un.L5
