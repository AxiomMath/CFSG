
module

public import CFSG.F3.Spec
public import CFSG.Monster.B.Fischer.Fi22CertBase

public section

namespace CFSG.Monster.B.Fischer

open CFSG.F3.Native CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  Matrix

@[expose] noncomputable def triMat (c : ℕ → ℕ) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  fun i j => if i ≤ j then (c (pairIdx i j) : ZMod 3) else 0

@[expose] noncomputable def quadM (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (v : Fi22V) : ZMod 3 :=
  v ⬝ᵥ (M *ᵥ v)

theorem quadM_apply (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (v : Fi22V) :
    quadM M v = ∑ i, ∑ j, M i j * v i * v j := by
  simp only [quadM, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fi22Quad_eq (c : ℕ → ℕ) (v : Fi22V) : fi22Quad c v = quadM (triMat c) v := by
  rw [quadM_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [triMat]
  split_ifs <;> ring

theorem quadM_mul (A M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (v : Fi22V) :
    quadM (Aᵀ * M * A) v = quadM M (A *ᵥ v) := by
  simp only [quadM]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem quadM_polar (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (u w : Fi22V) :
    quadM M (u + w) - quadM M u - quadM M w = u ⬝ᵥ ((M + Mᵀ) *ᵥ w) := by
  simp only [quadM, mulVec_add, add_dotProduct, dotProduct_add, add_mulVec]
  rw [dotProduct_comm w (M *ᵥ u), ← vecMul_transpose, ← dotProduct_mulVec]
  ring

theorem quadM_eq_sym (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (v : Fi22V) :
    quadM M v = ∑ i, ∑ j, if i ≤ j then
      (if i = j then M i i else M i j + M j i) * v i * v j else 0 := by
  rw [quadM_apply]
  have hsplit : ∀ i j : Fin 77, M i j * v i * v j =
      (if i ≤ j then M i j * v i * v j else 0) + (if j < i then M i j * v i * v j else 0) := by
    intro i j
    rcases le_or_gt i j with h | h
    · simp [h, not_lt.2 h]
    · simp [h, not_le.2 h]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then M i j * v i * v j else 0),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, h, h.ne]
    ring
  · simp
  · simp [not_le.2 h, not_lt.2 h.le]

theorem formRows_getElem (b : ByteArray) (off : ℕ) {i : ℕ} (hi : i < 77) :
    (formRows b off)[i]! =
      V.ofFn 77 fun j => if i ≤ j then trit b off (pairIdx i j) else 0 := by
  rw [formRows, getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]

theorem rowsWF_formRows (b : ByteArray) (off : ℕ) : RowsWF (formRows b off) := by
  intro j
  by_cases hj : j < 77
  · rw [formRows_getElem b off hj]
    exact V.wf_ofFn _ _
  · rw [getElem!_neg _ j (by simp [formRows, hj])]
    rfl

theorem formRows_size (b : ByteArray) (off : ℕ) : (formRows b off).size = 77 := by
  simp [formRows]

theorem toMat_formRows (b : ByteArray) (off : ℕ) :
    toMat 77 (formRows b off) = triMat (trit b off) := by
  ext i j
  rw [toMat_apply, formRows_getElem b off i.2, V.val_ofFn, ite_eq_left j.2, triMat]
  simp only [Fin.le_def]
  split_ifs <;> simp

theorem polarRows_getElem (b : ByteArray) (off : ℕ) {i : ℕ} (hi : i < 77) :
    (polarRows b off)[i]! = (formRows b off)[i]!.add (transpose 77 (formRows b off))[i]! := by
  rw [polarRows, getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]

theorem rowsWF_polarRows (b : ByteArray) (off : ℕ) : RowsWF (polarRows b off) := by
  intro j
  by_cases hj : j < 77
  · rw [polarRows_getElem b off hj]
    exact V.wf_add (rowsWF_formRows b off j) (RowsWF.transpose 77 _ j)
  · rw [getElem!_neg _ j (by simp [polarRows, hj])]
    rfl

theorem polarRows_size (b : ByteArray) (off : ℕ) : (polarRows b off).size = 77 := by
  simp [polarRows]

theorem toMat_polarRows (b : ByteArray) (off : ℕ) :
    toMat 77 (polarRows b off) = triMat (trit b off) + (triMat (trit b off))ᵀ := by
  ext i j
  rw [toMat_apply, polarRows_getElem b off i.2,
    V.val_add (rowsWF_formRows b off i) (RowsWF.transpose 77 _ i), Matrix.add_apply,
    ← toMat_formRows, ← toMat_transpose, toMat_apply, toMat_apply]

theorem single_dotProduct_mulVec_single (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) (i j : Fin 77) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  rw [mulVec_single_one, single_dotProduct, one_mul]
  rfl

theorem quadM_polarMatrix (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) :
    polarMatrix (quadM M) = M + Mᵀ := by
  ext i j
  rw [polarMatrix, quadM_polar, single_dotProduct_mulVec_single]

theorem polarMatrix_fi22Quad (c : ℕ → ℕ) :
    polarMatrix (fi22Quad c) = triMat c + (triMat c)ᵀ := by
  rw [show fi22Quad c = quadM (triMat c) from funext (fi22Quad_eq c), quadM_polarMatrix]

theorem fi22Quad_polar (c : ℕ → ℕ) (u w : Fi22V) :
    fi22Quad c (u + w) - fi22Quad c u - fi22Quad c w = u ⬝ᵥ (polarMatrix (fi22Quad c) *ᵥ w) := by
  rw [fi22Quad_eq, fi22Quad_eq, fi22Quad_eq, quadM_polar, polarMatrix_fi22Quad]

theorem natCast_coefAt (C : Array V) (i j : ℕ) :
    (coefAt C i j : ZMod 3) =
      if i = j then C[i]!.val i else C[i]!.val j + C[j]!.val i := by
  unfold coefAt V.val
  split_ifs
  · rfl
  · rw [ZMod.natCast_mod, Nat.cast_add]

theorem coefOK_spec {C : Array V} {b : ByteArray} {off : ℕ} (h : coefOK C b off = true)
    (v : Fi22V) : quadM (toMat 77 C) v = fi22Quad (trit b off) v := by
  unfold coefOK at h
  rw [allLt_iff] at h
  rw [quadM_eq_sym, fi22Quad]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hij := allLt_iff.1 (h i i.2) j j.2
  by_cases hle : i ≤ j
  · rw [ite_eq_left hle, ite_eq_left hle]
    have hle' : (i : ℕ) ≤ j := hle
    simp only [hle', decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hij
    congr 2
    rw [← hij, natCast_coefAt]
    simp only [Fin.val_inj, toMat_apply]
  · rw [ite_eq_right hle, ite_eq_right hle]

theorem rowsWF_transpose_size (A : Array V) : (transpose 77 A).size = 77 := by
  simp [CFSG.F3.Native.transpose]

theorem pullbackOK_spec {b bTo : ByteArray} {off offTo : ℕ} {A : Array V} (hA : RowsWF A)
    (h : pullbackOK b off bTo offTo A (transpose 77 A) = true) (v : Fi22V) :
    fi22Quad (trit b off) v = fi22Quad (trit bTo offTo) (toMat 77 A *ᵥ v) := by
  unfold pullbackOK at h
  rw [← coefOK_spec h, toMat_mul (rowsWF_transpose_size A) (RowsWF.transpose 77 A)
    (RowsWF.mul _ 77 (rowsWF_formRows bTo offTo) hA), toMat_mul (formRows_size bTo offTo)
    (rowsWF_formRows bTo offTo) hA, toMat_transpose, toMat_formRows, ← mul_assoc, quadM_mul,
    fi22Quad_eq]

theorem fi22Quad_coeff (c : ℕ → ℕ) {i j : Fin 77} (hij : i ≤ j) :
    (c (pairIdx i j) : ZMod 3) = if i = j then fi22Quad c (Pi.single i 1)
      else polarMatrix (fi22Quad c) i j := by
  split_ifs with h
  · subst h
    rw [fi22Quad_eq, quadM, single_dotProduct_mulVec_single, triMat, ite_eq_left le_rfl]
  · rw [polarMatrix_fi22Quad, Matrix.add_apply, Matrix.transpose_apply, triMat, triMat,
      ite_eq_left hij, ite_eq_right (not_le.2 (lt_of_le_of_ne hij h)), add_zero]

theorem natCast_inj_of_lt_three {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  interval_cases a <;> interval_cases b <;> first | rfl | exact absurd h (by decide)

theorem fi22Quad_ne {c c' : ℕ → ℕ} (hc : ∀ k, c k < 3) (hc' : ∀ k, c' k < 3) {i j : Fin 77}
    (hij : i ≤ j) (hne : c (pairIdx i j) ≠ c' (pairIdx i j)) : fi22Quad c ≠ fi22Quad c' := by
  intro h
  apply hne
  apply natCast_inj_of_lt_three (hc _) (hc' _)
  rw [fi22Quad_coeff c hij, fi22Quad_coeff c' hij, h]

end CFSG.Monster.B.Fischer
