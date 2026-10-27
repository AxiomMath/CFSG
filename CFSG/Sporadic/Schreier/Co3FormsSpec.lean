module

public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Sporadic.Schreier.Co3CertBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Matrix

@[expose] noncomputable def triMat (t : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  fun i j => if i ≤ j then co3Coef t i j else 0

@[expose] noncomputable def quadM (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (v : Co3V) : ZMod 2 :=
  v ⬝ᵥ (M *ᵥ v)

theorem quadM_apply (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (v : Co3V) :
    quadM M v = ∑ i, ∑ j, M i j * v i * v j := by
  simp only [quadM, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem co3Quad_eq (t : ℕ) (v : Co3V) : co3Quad t v = quadM (triMat t) v := by
  rw [quadM_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [triMat]
  split_ifs <;> ring

theorem quadM_mul (A M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (v : Co3V) :
    quadM (Aᵀ * M * A) v = quadM M (A *ᵥ v) := by
  simp only [quadM]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem quadM_eq_sym (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (v : Co3V) :
    quadM M v = ∑ i, ∑ j, if i ≤ j then
      (if i = j then M i i else M i j + M j i) * v i * v j else 0 := by
  rw [quadM_apply]
  have hsplit : ∀ i j : Fin 22, M i j * v i * v j =
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

theorem toVecD_testBit (x : ℕ) (j : Fin 22) :
    toVecD 22 x j = if x.testBit j.val then 1 else 0 := rfl

theorem rowsMatrix_triRows (t : ℕ) : rowsMatrix 22 (triRows t) = triMat t := by
  ext i j
  rw [rowsMatrix_apply, triRows, Array.getElem?_ofFn, dite_eq_left i.2, Option.getD_some,
    toVecD_ofBits, triMat, co3Coef]
  simp only [Fin.le_def]
  split_ifs <;> simp_all

theorem rowsMatrix_apply' (C : Array ℕ) (i j : Fin 22) :
    rowsMatrix 22 C i j = if (C[i.val]?.getD 0).testBit j.val then 1 else 0 := rfl

theorem bool_xor_cast (a b : Bool) :
    ((if (a ^^ b) then 1 else 0 : ZMod 2)) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem coefOK_spec {C : Array ℕ} {t : ℕ} (h : coefOK C t = true) (v : Co3V) :
    quadM (rowsMatrix 22 C) v = co3Quad t v := by
  unfold coefOK at h
  rw [allLt_iff] at h
  rw [quadM_eq_sym, co3Quad]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hij := allLt_iff.1 (h i i.2) j j.2
  by_cases hle : i ≤ j
  · rw [ite_eq_left hle, ite_eq_left hle]
    have hle' : (i : ℕ) ≤ j := hle
    simp only [hle', decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hij
    congr 2
    unfold coefBit at hij
    rw [co3Coef, ← hij]
    by_cases hij' : i = j
    · subst hij'
      simp [rowsMatrix_apply']
    · have hne : (i : ℕ) ≠ j := fun e => hij' (Fin.ext e)
      rw [ite_eq_right hij', ite_eq_right hne, bool_xor_cast, rowsMatrix_apply',
        rowsMatrix_apply']
  · rw [ite_eq_right hle, ite_eq_right hle]

theorem pullOK_spec {A : Array ℕ} {t t' : ℕ} (h : pullOK A t t' = true) (v : Co3V) :
    co3Quad t v = co3Quad t' (rowsMatrix 22 A *ᵥ v) := by
  unfold pullOK at h
  rw [← coefOK_spec h, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows,
    rowsMatrix_triRows, ← mul_assoc, quadM_mul, co3Quad_eq]

theorem single_dotProduct_mulVec_single (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (i j : Fin 22) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  rw [mulVec_single_one, single_dotProduct, one_mul]
  rfl

theorem quadM_single_add (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (i j : Fin 22) :
    quadM M (Pi.single i 1 + Pi.single j 1) - quadM M (Pi.single i 1) -
      quadM M (Pi.single j 1) = M i j + M j i := by
  simp only [quadM, mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct_mulVec_single]
  ring

theorem co3Quad_coeff (t : ℕ) {i j : Fin 22} (hij : i ≤ j) :
    co3Coef t i j = if i = j then co3Quad t (Pi.single i 1) else
      co3Quad t (Pi.single i 1 + Pi.single j 1) - co3Quad t (Pi.single i 1) -
        co3Quad t (Pi.single j 1) := by
  split_ifs with h
  · subst h
    rw [co3Quad_eq, quadM, single_dotProduct_mulVec_single, triMat, ite_eq_left le_rfl]
  · rw [co3Quad_eq, co3Quad_eq, co3Quad_eq, quadM_single_add, triMat, triMat, ite_eq_left hij,
      ite_eq_right (not_le.2 (lt_of_le_of_ne hij h)), add_zero]

theorem co3Coef_eq_iff {t t' : ℕ} {i j : ℕ} :
    co3Coef t i j = co3Coef t' i j ↔ t.testBit (pairIdx22 i j) = t'.testBit (pairIdx22 i j) := by
  unfold co3Coef
  cases t.testBit (pairIdx22 i j) <;> cases t'.testBit (pairIdx22 i j) <;> decide

theorem pairIdx22_surj {k : ℕ} (hk : k < 253) :
    ∃ i < 22, ∃ j < 22, i ≤ j ∧ pairIdx22 i j = k := by
  revert k
  decide +kernel

theorem co3Quad_injective {t t' : ℕ} (ht : t < 2 ^ 253) (ht' : t' < 2 ^ 253)
    (h : co3Quad t = co3Quad t') : t = t' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 253
  · obtain ⟨i, hi, j, hj, hij, rfl⟩ := pairIdx22_surj hk
    have hij' : (⟨i, hi⟩ : Fin 22) ≤ ⟨j, hj⟩ := hij
    have e := co3Quad_coeff t hij'
    rw [h, ← co3Quad_coeff t' hij'] at e
    exact co3Coef_eq_iff.1 e
  · have hle : 2 ^ 253 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ht hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht' hle)]

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  have h := ZMod.pow_card (p := 2) x
  rwa [sq] at h

theorem co3Quad_sub_of_offDiagOK {t t' : ℕ} (h : offDiagOK t t' = true) (v : Co3V) :
    co3Quad t v - co3Quad t' v = ∑ i : Fin 22, (co3Coef t i i - co3Coef t' i i) * v i := by
  have hoff : ∀ i j : Fin 22, i < j → co3Coef t i j = co3Coef t' i j := by
    intro i j hij
    unfold offDiagOK at h
    have hj := allLt_iff.1 (allLt_iff.1 h i i.2) j j.2
    have hij' : (i : ℕ) < j := hij
    simp only [hij', decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hj
    exact co3Coef_eq_iff.2 hj
  have hterm : ∀ i j : Fin 22,
      (if i ≤ j then co3Coef t i j * v i * v j else 0) =
        (if i ≤ j then co3Coef t' i j * v i * v j else 0) +
          if j = i then (co3Coef t i i - co3Coef t' i i) * v i else 0 := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [ite_eq_left hij.le, ite_eq_left hij.le, hoff i j hij, ite_eq_right (ne_of_gt hij),
        add_zero]
    · rw [ite_eq_left le_rfl, ite_eq_left le_rfl, ite_eq_left rfl]
      linear_combination (co3Coef t i i - co3Coef t' i i) * zmod2_mul_self (v i)
    · rw [ite_eq_right (not_le.2 hij), ite_eq_right (not_le.2 hij), ite_eq_right (ne_of_lt hij),
        add_zero]
  refine (sub_eq_iff_eq_add').2 ?_
  rw [co3Quad, co3Quad, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD : (co3Coef t i i - co3Coef t' i i) * v i =
      ∑ j : Fin 22, if j = i then (co3Coef t i i - co3Coef t' i i) * v i else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp
  rw [hD, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hterm i j

end CFSG.Sporadic.Schreier.Co3
