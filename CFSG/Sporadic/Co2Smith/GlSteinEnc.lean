module

public import CFSG.Sporadic.Co2Smith.GlSteinRoots
public import CFSG.Sporadic.Co2Smith.GlU62SteinInputs

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.Fischer
  CFSG.LieType.Universal.Unitary.SUExtras Native

attribute [local instance high] f4DecEq

@[expose] def k6Row (k : Fin 36) : Fin 6 := ⟨k.val / 6, by omega⟩

@[expose] def k6Col (k : Fin 36) : Fin 6 := ⟨k.val % 6, by omega⟩

@[expose] def m6Arr (M : Matrix (Fin 6) (Fin 6) F4) : Array F4 :=
  Array.ofFn fun k : Fin 36 => M (k6Row k) (k6Col k)

theorem m6Arr_size (M : Matrix (Fin 6) (Fin 6) F4) : (m6Arr M).size = 36 := by
  simp only [m6Arr, Array.size_ofFn]

theorem m6Arr_getElem (M : Matrix (Fin 6) (Fin 6) F4) (k : ℕ) (hk : k < (m6Arr M).size) :
    (m6Arr M)[k] = M (k6Row ⟨k, by rw [m6Arr_size] at hk; exact hk⟩)
      (k6Col ⟨k, by rw [m6Arr_size] at hk; exact hk⟩) := by
  simp only [m6Arr, Array.getElem_ofFn]

theorem m6Get_m6Arr (M : Matrix (Fin 6) (Fin 6) F4) (i j : Fin 6) :
    m6Get (m6Arr M) i j = M i j := by
  have hk : 6 * i.val + j.val < (m6Arr M).size := by rw [m6Arr_size]; omega
  rw [m6Get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
    m6Arr_getElem]
  congr 1
  · ext
    simp only [k6Row]
    omega
  · ext
    simp only [k6Col]
    omega

theorem m6Mul_m6Arr (M N : Matrix (Fin 6) (Fin 6) F4) :
    m6Mul (m6Arr M) (m6Arr N) = m6Arr (M * N) := by
  apply Array.ext
  · simp only [m6Mul, Array.size_ofFn, m6Arr_size]
  · intro k hk1 hk2
    have hk : k < 36 := by rwa [m6Arr_size] at hk2
    rw [m6Arr_getElem, Matrix.mul_apply, Fin.sum_univ_six]
    simp only [m6Mul, Array.getElem_ofFn]
    have e : ∀ l : Fin 6, m6Get (m6Arr M) (k / 6) l * m6Get (m6Arr N) l (k % 6) =
        M (k6Row ⟨k, hk⟩) l * N l (k6Col ⟨k, hk⟩) := fun l => by
      rw [show k / 6 = (k6Row ⟨k, hk⟩).val from rfl, m6Get_m6Arr,
        show k % 6 = (k6Col ⟨k, hk⟩).val from rfl, m6Get_m6Arr]
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    have e4 := e 4
    have e5 := e 5
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
    rw [show ((3 : Fin 6) : ℕ) = 3 from rfl] at e3
    rw [show ((4 : Fin 6) : ℕ) = 4 from rfl] at e4
    rw [show ((5 : Fin 6) : ℕ) = 5 from rfl] at e5
    rw [e0, e1, e2, e3, e4, e5]

theorem m6One_eq : m6One = m6Arr 1 := by
  apply Array.ext
  · simp only [m6One, Array.size_ofFn, m6Arr_size]
  · intro k hk1 hk2
    rw [m6Arr_getElem, Matrix.one_apply]
    simp only [m6One, Array.getElem_ofFn, k6Row, k6Col, Fin.mk.injEq]

theorem rootMatrix_entry (i j a b : Fin 6) (c : F4) :
    rootMatrix su6σ i j c a b = (if a = b then 1 else 0) + (if i = a ∧ j = b then c else 0) +
      (if Fin.rev j = a ∧ Fin.rev i = b then c * c else 0) := by
  have hneg : ∀ x : F4, -x = x := fun _ => rfl
  simp only [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, su6σ_apply, sub_eq_add_neg, hneg]

theorem longRootMatrix_entry (i a b : Fin 6) (c : F4) :
    longRootMatrix i c a b = (if a = b then 1 else 0) +
      (if i = a ∧ Fin.rev i = b then c else 0) := by
  simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem stPosI_eq : ∀ r : Fin 18, stPosI.getD r.val 0 = (su6Pos r).1.val := by decide

theorem stPosJ_eq : ∀ r : Fin 18, stPosJ.getD r.val 0 = (su6Pos r).2.val := by decide

theorem f4c_code (c : F4) : f4c c.code.val = c := by
  obtain ⟨k⟩ := c
  show F4.mk _ = F4.mk k
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt k.isLt)

theorem fin6_rev_val (j : Fin 6) : (Fin.rev j).val = 5 - j.val := by
  simp [Fin.val_rev]

theorem m6Arr_rootMatrix (i j : Fin 6) (c : F4) :
    m6Arr (rootMatrix su6σ i j c) = stEltS i.val j.val c.code.val := by
  apply Array.ext
  · simp only [stEltS, Array.size_ofFn, m6Arr_size]
  · intro k hk1 hk2
    rw [m6Arr_getElem, rootMatrix_entry]
    simp only [stEltS, Array.getElem_ofFn, f4c_code, Fin.ext_iff, fin6_rev_val, k6Row, k6Col]

theorem m6Arr_longRootMatrix (i : Fin 6) :
    m6Arr (longRootMatrix i 1) = stEltL i.val (Fin.rev i).val 1 := by
  apply Array.ext
  · simp only [stEltL, Array.size_ofFn, m6Arr_size]
  · intro k hk1 hk2
    rw [m6Arr_getElem, longRootMatrix_entry]
    have h1 : (1 : ℕ) % 4 ≠ 0 := by decide
    simp only [stEltL, Array.getElem_ofFn, Fin.ext_iff, k6Row, k6Col, h1, ne_eq,
      not_false_eq_true, and_true]

theorem stEltL_congr (i j : ℕ) {c d : ℕ} (h : c % 4 ≠ 0 ↔ d % 4 ≠ 0) :
    stEltL i j c = stEltL i j d := by
  simp only [stEltL, h]

theorem m6Arr_one (i j : ℕ) : m6Arr (1 : Matrix (Fin 6) (Fin 6) F4) = stEltL i j 0 := by
  apply Array.ext
  · simp only [stEltL, Array.size_ofFn, m6Arr_size]
  · intro k hk1 hk2
    rw [m6Arr_getElem, Matrix.one_apply]
    simp only [stEltL, Array.getElem_ofFn, Fin.ext_iff, k6Row, k6Col]
    simp

theorem m6Arr_su6Elt (r : Fin 18) (c : F4) :
    m6Arr (mat su6σ 6 (su6Elt r c)) = stElt r.val c.code.val := by
  rw [stElt, stPosI_eq, stPosJ_eq]
  by_cases hr : r.val < 12
  · rw [ite_eq_left hr, su6Elt, ite_eq_left hr, mat_apply, coe_rootHom, toAdd_ofAdd,
      m6Arr_rootMatrix]
  · rw [ite_eq_right hr, su6Pos_long r (by omega)]
    by_cases hc : c = 0
    · subst hc
      rw [su6Elt, ite_eq_right hr, ite_eq_left rfl, map_one, m6Arr_one]
      rfl
    · rw [su6Elt, ite_eq_right hr, ite_eq_right hc, mat_apply, coe_longRootHom, toAdd_ofAdd,
        m6Arr_longRootMatrix]
      refine stEltL_congr _ _ ⟨fun _ => ?_, fun _ => by decide⟩
      intro h
      apply hc
      rw [F4.eq_iff_code]
      exact Fin.ext (by rw [Nat.mod_eq_of_lt c.code.isLt] at h; exact h)

end CFSG.Sporadic.Co2Smith
