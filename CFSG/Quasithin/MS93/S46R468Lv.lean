module

public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S46R

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def stabE0 : Subgroup (SL3 F) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1}
  mul_mem' := fun {A B} hA hB => by
    show ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) =
      Pi.single 0 1
    rw [coe_mul_SL3, ← mulVec_mulVec,
      show ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) =
        Pi.single 0 1 from hB]
    exact hA
  one_mem' := by
    show ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1
    rw [coe_one_SL3, one_mulVec]
  inv_mem' := fun {A} hA => by
    show ((A⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) =
      Pi.single 0 1
    have hA' : ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) =
        Pi.single 0 1 := hA
    conv_lhs => rw [← hA']
    rw [mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, one_mulVec]

theorem mem_stabE0 {A : SL3 F} :
    A ∈ stabE0 ↔ (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 :=
  Iff.rfl

theorem mulVec_single_one_apply (A : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    (A *ᵥ (Pi.single j 1 : Fin 3 → F)) i = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem col_zero_of_mem_stabE0 {A : SL3 F} (hA : A ∈ stabE0) (i : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) i 0 = if i = 0 then 1 else 0 := by
  have h := congrFun (mem_stabE0.mp hA) i
  rw [mulVec_single_one_apply] at h
  rw [h, Pi.single_apply]

theorem mem_stabE0_of_col {A : SL3 F}
    (hA : ∀ i : Fin 3, (A : Matrix (Fin 3) (Fin 3) F) i 0 = if i = 0 then 1 else 0) :
    A ∈ stabE0 := by
  rw [mem_stabE0]
  funext i
  rw [mulVec_single_one_apply, hA i, Pi.single_apply]

theorem sStar_le_stabE0 : (sStar : Subgroup (SL3 F)) ≤ stabE0 := by
  intro g hg
  obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hg
  refine mem_stabE0_of_col fun i => ?_
  rw [coe_uniTri]
  fin_cases i <;> simp

theorem qLn_le_stabE0 : (qLn : Subgroup (SL3 F)) ≤ stabE0 :=
  qLn_le_sStar.trans sStar_le_stabE0

theorem entry_of_sub_mem_pt0 {A : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ v : Fin 3 → F, A *ᵥ v - v ∈ pt0) {i : Fin 3} (hi : i ≠ 0) (j : Fin 3) :
    A i j = if i = j then 1 else 0 := by
  have hv := mem_pt0.mp (h (Pi.single j 1))
  have hc : (A *ᵥ (Pi.single j 1 : Fin 3 → F) - (Pi.single j 1 : Fin 3 → F)) i = 0 := by
    fin_cases i
    · exact absurd rfl hi
    · exact hv.1
    · exact hv.2
  rw [Pi.sub_apply, sub_eq_zero, mulVec_single_one_apply] at hc
  rw [hc, Pi.single_apply]

theorem sub_mem_pt0_of_entry {A : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ i j : Fin 3, i ≠ 0 → A i j = if i = j then 1 else 0) (v : Fin 3 → F) :
    A *ᵥ v - v ∈ pt0 := by
  have h10 := h 1 0 (by decide)
  have h11 := h 1 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h20 := h 2 0 (by decide)
  have h21 := h 2 1 (by decide)
  have h22 := h 2 2 (by decide)
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true] at h10 h11 h12 h20 h21 h22
  rw [mem_pt0]
  constructor <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h11, h12, h20, h21, h22]

theorem mem_stabE0_of_sub_mem_pt0 {A : SL3 F}
    (h : ∀ v : Fin 3 → F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0) : A ∈ stabE0 := by
  have h10 := entry_of_sub_mem_pt0 h (i := 1) (by decide) 0
  have h11 := entry_of_sub_mem_pt0 h (i := 1) (by decide) 1
  have h12 := entry_of_sub_mem_pt0 h (i := 1) (by decide) 2
  have h20 := entry_of_sub_mem_pt0 h (i := 2) (by decide) 0
  have h21 := entry_of_sub_mem_pt0 h (i := 2) (by decide) 1
  have h22 := entry_of_sub_mem_pt0 h (i := 2) (by decide) 2
  simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true] at h10 h11 h12 h20 h21 h22
  have hdet := A.2
  rw [Matrix.det_fin_three, h10, h11, h12, h20, h21, h22] at hdet
  have h00 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by linear_combination hdet
  refine mem_stabE0_of_col fun i => ?_
  fin_cases i
  · simpa using h00
  · simpa using h10
  · simpa using h20

theorem sub_mem_pt0_iff_mem_qPt {A : SL3 F} :
    (∀ v : Fin 3 → F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0) ↔ A ∈ qPt := by
  constructor
  · intro h
    have h0 := col_zero_of_mem_stabE0 (mem_stabE0_of_sub_mem_pt0 h)
    have h11 := entry_of_sub_mem_pt0 h (i := 1) (by decide) 1
    have h12 := entry_of_sub_mem_pt0 h (i := 1) (by decide) 2
    have h21 := entry_of_sub_mem_pt0 h (i := 2) (by decide) 1
    have h22 := entry_of_sub_mem_pt0 h (i := 2) (by decide) 2
    simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true] at h11 h12 h21 h22
    refine mem_qPt_iff_uniTri.mpr ⟨(A : Matrix (Fin 3) (Fin 3) F) 0 1,
      (A : Matrix (Fin 3) (Fin 3) F) 0 2, ?_⟩
    apply Subtype.ext
    rw [coe_uniTri]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h11, h12, h21, h22]
  · intro hA
    obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp hA
    refine sub_mem_pt0_of_entry fun i j hi => ?_
    rw [coe_uniTri]
    fin_cases i <;> fin_cases j <;> simp at hi ⊢

@[expose] noncomputable def blockE0 : ↥(stabE0 : Subgroup (SL3 F)) →* SL(2, F) where
  toFun A := ⟨(A : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ, by
    have h0 := col_zero_of_mem_stabE0 A.2
    have hd := (A : SL3 F).2
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at hd
    simp only [h0, Fin.succ_ne_zero, ite_true, ite_false, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, pow_zero, one_mul, Fin.val_zero] at hd
    rw [show (Fin.succAbove (0 : Fin 3)) = Fin.succ from rfl] at hd
    exact hd⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [Matrix.one_apply, Fin.succ_inj]
  map_mul' A B := by
    apply Subtype.ext
    ext i j
    have hA := col_zero_of_mem_stabE0 A.2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.submatrix_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, hA, Fin.succ_ne_zero, ite_false, zero_mul, zero_add]
    rfl

theorem blockE0_apply (A : ↥(stabE0 : Subgroup (SL3 F))) (i j : Fin 2) :
    ((blockE0 A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) i.succ j.succ :=
  rfl

@[expose] noncomputable def liftE0 (B : SL(2, F)) : SL3 F :=
  ⟨Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => (B : Matrix (Fin 2) (Fin 2) F) i' j') j) i, by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, pow_zero,
      one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [show (Fin.succAbove (0 : Fin 3)) = Fin.succ from rfl]
    have hB := B.2
    convert hB using 2
    ext i j
    simp⟩

theorem liftE0_mem (B : SL(2, F)) : liftE0 B ∈ (stabE0 : Subgroup (SL3 F)) := by
  refine mem_stabE0_of_col fun i => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [liftE0, Fin.succ_ne_zero]

theorem blockE0_liftE0 (B : SL(2, F)) : blockE0 ⟨liftE0 B, liftE0_mem B⟩ = B := by
  apply Subtype.ext
  ext i j
  simp [blockE0_apply, liftE0]

theorem blockE0_eq_one_iff (A : ↥(stabE0 : Subgroup (SL3 F))) :
    blockE0 A = 1 ↔ ∀ v : Fin 3 → F, ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ pt0 := by
  have h0 := col_zero_of_mem_stabE0 A.2
  constructor
  · intro h
    refine sub_mem_pt0_of_entry fun i j hi => ?_
    have hb : ∀ i j : Fin 2, ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F) i.succ j.succ =
        if i = j then 1 else 0 := fun i j => by
      rw [← blockE0_apply, h]
      simp [Matrix.one_apply]
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hi
    refine Fin.cases ?_ (fun j => ?_) j
    · exact h0 _
    · rw [hb]
      simp [Fin.succ_inj]
  · intro h
    apply Subtype.ext
    ext i j
    rw [blockE0_apply, entry_of_sub_mem_pt0 h (Fin.succ_ne_zero i)]
    simp [Matrix.one_apply, Fin.succ_inj]

theorem coe_blockE0_uniTri (a b c : F) :
    ((blockE0 ⟨uniTri a b c, sStar_le_stabE0 (mem_sStar_iff.mpr ⟨a, b, c, rfl⟩)⟩ : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := by
  ext i j
  rw [blockE0_apply]
  change ((uniTri a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) i.succ j.succ = _
  rw [coe_uniTri]
  fin_cases i <;> fin_cases j <;> rfl

end CFSG.Quasithin.MS93.S46R
