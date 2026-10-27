module

public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Sporadic.Schreier.PairF2

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def pairIdx (d i j : ℕ) : ℕ := d * i - i * (i - 1) / 2 + (j - i)

@[expose] def monomials (d : ℕ) : List (ℕ × ℕ) :=
  (List.range d).flatMap fun i => (List.range (d - i)).map fun k => (i, i + k)

@[expose] def coefZ (d z i j : ℕ) : ZMod 2 := if z.testBit (pairIdx d i j) then 1 else 0

@[expose] def quadZ (d z : ℕ) (v : Fin d → ZMod 2) : ZMod 2 :=
  ∑ i : Fin d, ∑ j : Fin d, if i ≤ j then coefZ d z i j * v i * v j else 0

@[expose] def polarMatrix {d : ℕ} (q : (Fin d → ZMod 2) → ZMod 2) :
    Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => q (Pi.single i 1 + Pi.single j 1) + q (Pi.single i 1) + q (Pi.single j 1)

@[expose] def triRowsZ (d z : ℕ) : Array ℕ :=
  Array.ofFn (n := d) fun i => ((z >>> pairIdx d i i) &&& (2 ^ (d - i.val) - 1)) <<< i.val

@[expose] def packRowsZ (d : ℕ) (U : Array ℕ) : ℕ :=
  (List.range d).foldl (fun acc i => acc ||| ((U[i]?.getD 0 >>> i) <<< pairIdx d i i)) 0

@[expose] def canonRows (d : ℕ) (C : Array ℕ) : Array ℕ :=
  let CT := transposeRows d C
  Array.ofFn (n := d) fun i =>
    ((((C[i.val]?.getD 0) ^^^ (CT[i.val]?.getD 0)) >>> (i.val + 1)) <<< (i.val + 1)) |||
      ((C[i.val]?.getD 0) &&& (1 <<< i.val))

@[expose] def pullOKZ (d : ℕ) (A : Array ℕ) (z z' : ℕ) : Bool :=
  canonRows d (mulRows d (transposeRows d A) (mulRows d (triRowsZ d z') A)) == triRowsZ d z

@[expose] def addRows (X Y : Array ℕ) : Array ℕ := Array.zipWith (· ^^^ ·) X Y

@[expose] def polarRowsZ (d z : ℕ) : Array ℕ :=
  addRows (triRowsZ d z) (transposeRows d (triRowsZ d z))

@[expose] def triMatZ (d z : ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => if i ≤ j then coefZ d z i j else 0

@[expose] def quadM {d : ℕ} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    ZMod 2 :=
  v ⬝ᵥ (M *ᵥ v)

variable {d : ℕ}

theorem quadM_apply (M : Matrix (Fin d) (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    quadM M v = ∑ i, ∑ j, M i j * v i * v j := by
  simp only [quadM, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadZ_eq (z : ℕ) (v : Fin d → ZMod 2) : quadZ d z v = quadM (triMatZ d z) v := by
  rw [quadM_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [triMatZ]
  split_ifs <;> ring

theorem quadM_mul (A M : Matrix (Fin d) (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    quadM (Aᵀ * M * A) v = quadM M (A *ᵥ v) := by
  simp only [quadM]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem quadM_eq_sym (M : Matrix (Fin d) (Fin d) (ZMod 2)) (v : Fin d → ZMod 2) :
    quadM M v = ∑ i, ∑ j, if i ≤ j then
      (if i = j then M i i else M i j + M j i) * v i * v j else 0 := by
  rw [quadM_apply]
  have hsplit : ∀ i j : Fin d, M i j * v i * v j =
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

theorem pairIdx_eq {i j : ℕ} : pairIdx d i j = pairIdx d i i + (j - i) := by
  simp [pairIdx]

theorem rowsMatrix_triRowsZ (z : ℕ) : rowsMatrix d (triRowsZ d z) = triMatZ d z := by
  ext i j
  rw [rowsMatrix_apply, triRowsZ, Array.getElem?_ofFn, dite_eq_left i.2, Option.getD_some,
    toVecD_apply, triMatZ, coefZ]
  rw [Nat.testBit_shiftLeft]
  by_cases hij : i ≤ j
  · have hij' : (i : ℕ) ≤ j := hij
    have hlt : (j : ℕ) - i < d - i := by have := j.2; omega
    have e : pairIdx d i j = pairIdx d i i + (j - i) := by simp [pairIdx]
    rw [ite_eq_left hij, e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    simp [hij', hlt]
  · have hij' : ¬ (i : ℕ) ≤ j := hij
    simp [hij', hij]

theorem testBit_transposeRows (C : Array ℕ) (i j : Fin d) :
    ((transposeRows d C)[i.val]?.getD 0).testBit j = (C[j.val]?.getD 0).testBit i := by
  unfold transposeRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [ofBits_testBit]
  simp [j.isLt]

theorem testBit_canonRows (C : Array ℕ) (i j : Fin d) :
    ((canonRows d C)[i.val]?.getD 0).testBit j =
      if (i : ℕ) < j then ((C[i.val]?.getD 0).testBit j ^^ (C[j.val]?.getD 0).testBit i)
      else if (i : ℕ) = j then (C[i.val]?.getD 0).testBit i else false := by
  have hT := testBit_transposeRows C i j
  simp only [canonRows, Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and,
    Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h1 : (i : ℕ) + 1 ≤ j := h
    have h3 : (i : ℕ) + 1 + (j - (i + 1)) = j := by omega
    have h4 : ¬ ((i : ℕ) = j) := by omega
    simp only [ge_iff_le, h1, decide_true, Bool.true_and, h3, h4, decide_false, Bool.and_false,
      Bool.or_false, ite_eq_left h, hT]
  · have h1 : ¬ (i : ℕ) + 1 ≤ j := by omega
    have hij : i = j := Fin.ext h
    subst hij
    simp [h1]
  · have h1 : ¬ (i : ℕ) + 1 ≤ j := by omega
    have h4 : ¬ ((i : ℕ) = j) := by omega
    have h5 : ¬ ((i : ℕ) < j) := by omega
    simp [h1, h4, h5]

theorem bool_xor_cast (a b : Bool) :
    ((if (a ^^ b) then 1 else 0 : ZMod 2)) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem canonRows_spec (C : Array ℕ) (v : Fin d → ZMod 2) :
    quadM (rowsMatrix d (canonRows d C)) v = quadM (rowsMatrix d C) v := by
  rw [quadM_eq_sym, quadM_eq_sym (rowsMatrix d C)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hle : i ≤ j
  · rw [ite_eq_left hle, ite_eq_left hle]
    congr 2
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, rowsMatrix_apply, toVecD_apply, testBit_canonRows, lt_irrefl,
        ite_false]
    · have hlt : (i : ℕ) < j := lt_of_le_of_ne hle fun e => hij (Fin.ext e)
      have hlt' : ¬ (j : ℕ) < i := by omega
      have hne : ¬ (j : ℕ) = i := by omega
      rw [ite_eq_right hij, ite_eq_right hij]
      simp only [rowsMatrix_apply, toVecD_apply, testBit_canonRows, ite_eq_left hlt, hlt', hne,
        ite_false, Bool.false_eq_true, add_zero]
      exact bool_xor_cast _ _
  · rw [ite_eq_right hle, ite_eq_right hle]

theorem pullOKZ_spec {A : Array ℕ} {z z' : ℕ} (h : pullOKZ d A z z' = true)
    (v : Fin d → ZMod 2) : quadZ d z v = quadZ d z' (rowsMatrix d A *ᵥ v) := by
  unfold pullOKZ at h
  rw [beq_iff_eq] at h
  rw [quadZ_eq, ← rowsMatrix_triRowsZ, ← h, canonRows_spec, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_transposeRows, rowsMatrix_triRowsZ, ← mul_assoc, quadM_mul, quadZ_eq]

theorem single_dotProduct_mulVec_single (M : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  rw [mulVec_single_one, single_dotProduct, one_mul]
  rfl

theorem quadM_single_add (M : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    quadM M (Pi.single i 1 + Pi.single j 1) + quadM M (Pi.single i 1) +
      quadM M (Pi.single j 1) = M i j + M j i := by
  simp only [quadM, mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct_mulVec_single]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  linear_combination (h2 (M i i)) + h2 (M j j)

theorem triMatZ_eq_of_quadZ_eq {z z' : ℕ} (h : quadZ d z = quadZ d z') :
    triMatZ d z = triMatZ d z' := by
  ext i j
  by_cases hij : i ≤ j
  · by_cases he : i = j
    · subst he
      have h1 := congrFun h (Pi.single i 1)
      rwa [quadZ_eq, quadZ_eq, quadM, quadM, single_dotProduct_mulVec_single,
        single_dotProduct_mulVec_single] at h1
    · have hji : ¬ j ≤ i := fun h' => he (le_antisymm hij h')
      have h1 := congrFun h (Pi.single i 1 + Pi.single j 1)
      have h2 := congrFun h (Pi.single i 1)
      have h3 := congrFun h (Pi.single j 1)
      rw [quadZ_eq, quadZ_eq] at h1 h2 h3
      have e := quadM_single_add (triMatZ d z) i j
      rw [h1, h2, h3, quadM_single_add] at e
      simpa [triMatZ, hji] using e.symm
  · simp [triMatZ, hij]

theorem triRowsZ_lt (z : ℕ) {i : ℕ} (hi : i < d) : (triRowsZ d z)[i]! < 2 ^ d := by
  have e : (triRowsZ d z)[i]! = ((z >>> pairIdx d i i) &&& (2 ^ (d - i) - 1)) <<< i := by
    unfold triRowsZ
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e, Nat.shiftLeft_eq]
  have h1 : (z >>> pairIdx d i i) &&& (2 ^ (d - i) - 1) < 2 ^ (d - i) :=
    Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) one_pos)
  calc _ < 2 ^ (d - i) * 2 ^ i := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos i)
    _ = 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]

theorem eq_of_quadZ_eq {z z' : ℕ} (hz : packRowsZ d (triRowsZ d z) = z)
    (hz' : packRowsZ d (triRowsZ d z') = z') (h : quadZ d z = quadZ d z') : z = z' := by
  have hlt : ∀ i < d, (triRowsZ d z)[i]! < 2 ^ d := fun i hi => triRowsZ_lt z hi
  have hlt' : ∀ i < d, (triRowsZ d z')[i]! < 2 ^ d := fun i hi => triRowsZ_lt z' hi
  have hm := triMatZ_eq_of_quadZ_eq h
  rw [← rowsMatrix_triRowsZ, ← rowsMatrix_triRowsZ] at hm
  have hrows : triRowsZ d z = triRowsZ d z' := by
    apply Array.ext (by simp [triRowsZ])
    intro i hi _
    have hi' : i < d := by simpa [triRowsZ] using hi
    have e : toVecD d (triRowsZ d z)[i]! = toVecD d (triRowsZ d z')[i]! := by
      funext j
      have := congrFun (congrFun hm ⟨i, hi'⟩) j
      rw [rowsMatrix_apply, rowsMatrix_apply] at this
      rw [getElem!_pos _ i (by simpa [triRowsZ] using hi'),
        getElem!_pos _ i (by simpa [triRowsZ] using hi')]
      simpa [Array.getElem?_eq_getElem (by simpa [triRowsZ] using hi' : i < (triRowsZ d z).size),
        Array.getElem?_eq_getElem (by simpa [triRowsZ] using hi' : i < (triRowsZ d z').size)]
        using this
    have := toVecD_injective (hlt i hi') (hlt' i hi') e
    rwa [getElem!_pos _ i (by simpa [triRowsZ] using hi'),
      getElem!_pos _ i (by simpa [triRowsZ] using hi')] at this
  rw [← hz, ← hz', hrows]

theorem rowsMatrix_addRows {X Y : Array ℕ} (hX : X.size = d) (hY : Y.size = d) :
    rowsMatrix d (addRows X Y) = rowsMatrix d X + rowsMatrix d Y := by
  ext i j
  have hi1 : i.val < X.size := by omega
  have hi2 : i.val < Y.size := by omega
  have hi3 : i.val < (addRows X Y).size := by simp [addRows]; omega
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply,
    Array.getElem?_eq_getElem hi1, Array.getElem?_eq_getElem hi2, Array.getElem?_eq_getElem hi3]
  simp only [Option.getD_some, addRows, Array.getElem_zipWith]
  rw [toVecD_xor, Pi.add_apply]

theorem polarMatrix_quadZ (z : ℕ) :
    polarMatrix (quadZ d z) = triMatZ d z + (triMatZ d z)ᵀ := by
  ext i j
  rw [polarMatrix, quadZ_eq, quadZ_eq, quadZ_eq, Matrix.add_apply, Matrix.transpose_apply,
    quadM_single_add]

theorem rowsMatrix_polarRowsZ (z : ℕ) :
    rowsMatrix d (polarRowsZ d z) = polarMatrix (quadZ d z) := by
  rw [polarRowsZ, rowsMatrix_addRows (by simp [triRowsZ]) (by simp [transposeRows]),
    rowsMatrix_transposeRows, rowsMatrix_triRowsZ, polarMatrix_quadZ]

theorem polar_quadZ (z : ℕ) (u v : Fin d → ZMod 2) :
    quadZ d z (u + v) + quadZ d z u + quadZ d z v = u ⬝ᵥ (polarMatrix (quadZ d z) *ᵥ v) := by
  rw [polarMatrix_quadZ, quadZ_eq, quadZ_eq, quadZ_eq]
  simp only [quadM, add_mulVec, mulVec_add, add_dotProduct, dotProduct_add]
  rw [show v ⬝ᵥ (triMatZ d z *ᵥ u) = u ⬝ᵥ ((triMatZ d z)ᵀ *ᵥ v) by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  linear_combination h2 (u ⬝ᵥ (triMatZ d z *ᵥ u)) + h2 (v ⬝ᵥ (triMatZ d z *ᵥ v))

end CFSG.Sporadic.Schreier.PairF2
