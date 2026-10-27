module

public import Mathlib
public import Certificates.Data.Schreier

public section

namespace CFSG

namespace M23.M23Group

@[expose] abbrev Perm23 := Equiv.Perm (Fin 23)

@[expose] def aFun : Fin 23 → Fin 23 :=
  ![1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def bFun : Fin 23 → Fin 23 :=
  ![15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def bInv : Fin 23 → Fin 23 :=
  ![2, 11, 10, 22, 3, 17, 6, 4, 1, 9, 15, 20, 19, 21, 16, 0, 14, 13, 18, 12, 8, 5, 7]

@[expose] def a : Perm23 :=
  { toFun := aFun
    invFun := aFun
    left_inv := by decide
    right_inv := by decide }

@[expose] def b : Perm23 :=
  { toFun := bFun
    invFun := bInv
    left_inv := by decide
    right_inv := by decide }

lemma a_apply (x : Fin 23) : a x = aFun x := rfl
lemma b_apply (x : Fin 23) : b x = bFun x := rfl

@[expose] def baseGen : Fin 2 → Perm23 := ![a, b]

@[expose] def word {n : Nat} (S : Fin n → Perm23) : List (Fin n × Bool) → Perm23 :=
  evalGroupWord S

@[expose] def g2Word : Perm23 := word baseGen
  [(0, true), (1, false), (0, false), (1, true), (0, false)]

@[expose] def g3Word : Perm23 := word baseGen
  [(1, true), (0, true), (1, true), (1, true), (0, false), (1, false)]

@[expose] def g4Word : Perm23 := word baseGen
  [(1, true), (1, true), (0, false), (1, false), (1, false)]

@[expose] def g5Word : Perm23 := word baseGen
  [(0, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false)]

@[expose] def g2Fun : Fin 23 → Fin 23 :=
  ![0, 4, 2, 3, 1, 5, 6, 22, 21, 14, 16, 12, 11, 19, 9, 15, 10, 18, 17, 13, 20, 8, 7]
@[expose] def g2InvFun : Fin 23 → Fin 23 :=
  ![0, 4, 2, 3, 1, 5, 6, 22, 21, 14, 16, 12, 11, 19, 9, 15, 10, 18, 17, 13, 20, 8, 7]
@[expose] def g2 : Perm23 :=
  { toFun := g2Fun, invFun := g2InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g3Fun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 7, 4, 2, 10, 3, 13, 20, 6, 15, 12, 8, 14, 11, 22, 19, 18, 17, 9, 21, 16]
@[expose] def g3InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 7, 4, 2, 10, 3, 13, 20, 6, 15, 12, 8, 14, 11, 22, 19, 18, 17, 9, 21, 16]
@[expose] def g3 : Perm23 :=
  { toFun := g3Fun, invFun := g3InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g4Fun : Fin 23 → Fin 23 :=
  ![0, 17, 14, 6, 4, 12, 3, 15, 8, 11, 20, 9, 5, 13, 2, 7, 16, 1, 19, 18, 10, 21, 22]
@[expose] def g4InvFun : Fin 23 → Fin 23 :=
  ![0, 17, 14, 6, 4, 12, 3, 15, 8, 11, 20, 9, 5, 13, 2, 7, 16, 1, 19, 18, 10, 21, 22]
@[expose] def g4 : Perm23 :=
  { toFun := g4Fun, invFun := g4InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g5Fun : Fin 23 → Fin 23 :=
  ![0, 15, 7, 8, 4, 21, 10, 6, 5, 18, 2, 16, 17, 13, 22, 1, 14, 9, 12, 20, 19, 3, 11]
@[expose] def g5InvFun : Fin 23 → Fin 23 :=
  ![0, 15, 10, 21, 4, 8, 7, 2, 3, 17, 6, 22, 18, 13, 16, 1, 11, 12, 9, 20, 19, 5, 14]
@[expose] def g5 : Perm23 :=
  { toFun := g5Fun, invFun := g5InvFun, left_inv := by decide, right_inv := by decide }

lemma g2_eq_word : g2 = g2Word := by
  ext x
  fin_cases x <;> decide
lemma g3_eq_word : g3 = g3Word := by
  ext x
  fin_cases x <;> decide
lemma g4_eq_word : g4 = g4Word := by
  ext x
  fin_cases x <;> decide
lemma g5_eq_word : g5 = g5Word := by
  ext x
  fin_cases x <;> decide

@[expose] def h1Gen : Fin 4 → Perm23 := ![g2, g3, g4, g5]

@[expose] def g6Word : Perm23 := word h1Gen [(1, false)]
@[expose] def g7Word : Perm23 := word h1Gen [(3, true), (3, true)]
@[expose] def g8Word : Perm23 := word h1Gen [(0, true), (1, false), (0, false)]
@[expose] def g9Word : Perm23 := word h1Gen [(0, true), (2, false), (0, false)]
@[expose] def g10Word : Perm23 := word h1Gen [(0, true), (3, false), (0, false)]

@[expose] def g6Fun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 7, 4, 2, 10, 3, 13, 20, 6, 15, 12, 8, 14, 11, 22, 19, 18, 17, 9, 21, 16]
@[expose] def g6InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 7, 4, 2, 10, 3, 13, 20, 6, 15, 12, 8, 14, 11, 22, 19, 18, 17, 9, 21, 16]
@[expose] def g6 : Perm23 :=
  { toFun := g6Fun, invFun := g6InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g7Fun : Fin 23 → Fin 23 :=
  ![0, 1, 6, 5, 4, 3, 2, 10, 21, 12, 7, 14, 9, 13, 11, 15, 22, 18, 17, 19, 20, 8, 16]
@[expose] def g7InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 6, 5, 4, 3, 2, 10, 21, 12, 7, 14, 9, 13, 11, 15, 22, 18, 17, 19, 20, 8, 16]
@[expose] def g7 : Perm23 :=
  { toFun := g7Fun, invFun := g7InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g8Fun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 22, 4, 2, 16, 10, 8, 9, 7, 11, 15, 18, 20, 12, 6, 17, 13, 21, 14, 19, 3]
@[expose] def g8InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 5, 22, 4, 2, 16, 10, 8, 9, 7, 11, 15, 18, 20, 12, 6, 17, 13, 21, 14, 19, 3]
@[expose] def g8 : Perm23 :=
  { toFun := g8Fun, invFun := g8InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g9Fun : Fin 23 → Fin 23 :=
  ![0, 1, 9, 6, 18, 11, 3, 7, 8, 2, 10, 5, 14, 17, 12, 22, 20, 13, 4, 19, 16, 21, 15]
@[expose] def g9InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 9, 6, 18, 11, 3, 7, 8, 2, 10, 5, 14, 17, 12, 22, 20, 13, 4, 19, 16, 21, 15]
@[expose] def g9 : Perm23 :=
  { toFun := g9Fun, invFun := g9InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g10Fun : Fin 23 → Fin 23 :=
  ![0, 1, 22, 21, 15, 8, 16, 12, 3, 7, 9, 18, 10, 20, 17, 4, 2, 11, 14, 19, 13, 5, 6]
@[expose] def g10InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 16, 8, 15, 21, 22, 9, 5, 10, 12, 17, 7, 20, 18, 4, 6, 14, 11, 19, 13, 3, 2]
@[expose] def g10 : Perm23 :=
  { toFun := g10Fun, invFun := g10InvFun, left_inv := by decide, right_inv := by decide }

lemma g6_eq_word : g6 = g6Word := by
  ext x
  fin_cases x <;> decide
lemma g7_eq_word : g7 = g7Word := by
  ext x
  fin_cases x <;> decide
lemma g8_eq_word : g8 = g8Word := by
  ext x
  fin_cases x <;> decide
lemma g9_eq_word : g9 = g9Word := by
  ext x
  fin_cases x <;> decide
lemma g10_eq_word : g10 = g10Word := by
  ext x
  fin_cases x <;> decide

@[expose] def h2Gen : Fin 5 → Perm23 := ![g6, g7, g8, g9, g10]

@[expose] def g11Word : Perm23 := word h2Gen [(0, true), (2, false)]
@[expose] def g12Word : Perm23 := word h2Gen [(4, false), (2, false), (1, false)]

@[expose] def g11Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 16, 4, 5, 22, 6, 13, 20, 3, 15, 11, 18, 9, 12, 10, 19, 8, 21, 14, 17, 7]
@[expose] def g11InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 10, 4, 5, 7, 22, 18, 14, 16, 12, 15, 8, 20, 11, 3, 21, 13, 17, 9, 19, 6]
@[expose] def g11 : Perm23 :=
  { toFun := g11Fun, invFun := g11InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g12Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 22, 15, 6, 8, 12, 19, 4, 9, 13, 7, 14, 18, 10, 21, 20, 11, 5, 17, 3, 16]
@[expose] def g12InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 21, 9, 19, 5, 12, 6, 10, 15, 18, 7, 11, 13, 4, 22, 20, 14, 8, 17, 16, 3]
@[expose] def g12 : Perm23 :=
  { toFun := g12Fun, invFun := g12InvFun, left_inv := by decide, right_inv := by decide }

lemma g11_eq_word : g11 = g11Word := by
  ext x
  fin_cases x <;> decide
lemma g12_eq_word : g12 = g12Word := by
  ext x
  fin_cases x <;> decide

@[expose] def h3Gen : Fin 2 → Perm23 := ![g11, g12]

@[expose] def g13Word : Perm23 := word h3Gen [(1, false), (1, false), (0, false)]

@[expose] def g14Word : Perm23 := word h3Gen
  [(0, false), (1, false), (0, true), (1, false), (0, false), (1, false)]

@[expose] def g15Word : Perm23 := word h3Gen
  [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false)]

@[expose] def g13Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 10, 8, 21, 19, 18, 20, 16, 9, 14, 13, 15, 12, 4, 6, 5, 22, 11, 17, 7]
@[expose] def g13InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 16, 18, 17, 22, 5, 11, 4, 20, 15, 13, 12, 14, 10, 21, 8, 7, 9, 6, 19]
@[expose] def g13 : Perm23 :=
  { toFun := g13Fun, invFun := g13InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g14Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 10, 7, 19, 21, 20, 18, 16, 6, 15, 12, 14, 13, 4, 9, 17, 11, 22, 5, 8]
@[expose] def g14InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 16, 21, 11, 5, 22, 17, 4, 19, 13, 15, 14, 12, 10, 18, 9, 6, 8, 7, 20]
@[expose] def g14 : Perm23 :=
  { toFun := g14Fun, invFun := g14InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g15Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 10, 20, 6, 9, 7, 8, 16, 19, 22, 17, 11, 5, 4, 21, 12, 14, 15, 13, 18]
@[expose] def g15InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 16, 15, 6, 8, 9, 7, 4, 14, 18, 21, 19, 20, 10, 13, 22, 11, 5, 17, 12]
@[expose] def g15 : Perm23 :=
  { toFun := g15Fun, invFun := g15InvFun, left_inv := by decide, right_inv := by decide }

lemma g13_eq_word : g13 = g13Word := by
  ext x
  fin_cases x <;> decide
lemma g14_eq_word : g14 = g14Word := by
  ext x
  fin_cases x <;> decide
lemma g15_eq_word : g15 = g15Word := by
  ext x
  fin_cases x <;> decide

@[expose] def h4Gen : Fin 3 → Perm23 := ![g13, g14, g15]

@[expose] def g16Word : Perm23 := word h4Gen [(0, true), (1, false)]
@[expose] def g17Word : Perm23 := word h4Gen [(0, false), (1, true)]
@[expose] def g18Word : Perm23 := word h4Gen [(0, true), (2, false)]
@[expose] def g19Word : Perm23 := word h4Gen [(0, false), (2, true)]

@[expose] def g16Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 22, 7, 6, 9, 8, 10, 17, 14, 15, 12, 13, 16, 11, 21, 20, 19, 18, 5]
@[expose] def g16InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 22, 7, 6, 9, 8, 10, 17, 14, 15, 12, 13, 16, 11, 21, 20, 19, 18, 5]
@[expose] def g16 : Perm23 :=
  { toFun := g16Fun, invFun := g16InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g17Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 17, 9, 8, 7, 6, 10, 22, 13, 12, 15, 14, 16, 5, 20, 21, 18, 19, 11]
@[expose] def g17InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 17, 9, 8, 7, 6, 10, 22, 13, 12, 15, 14, 16, 5, 20, 21, 18, 19, 11]
@[expose] def g17 : Perm23 :=
  { toFun := g17Fun, invFun := g17InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g18Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 9, 17, 11, 22, 5, 10, 7, 19, 21, 20, 18, 16, 6, 15, 12, 14, 13, 8]
@[expose] def g18InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 9, 17, 11, 22, 5, 10, 7, 19, 21, 20, 18, 16, 6, 15, 12, 14, 13, 8]
@[expose] def g18 : Perm23 :=
  { toFun := g18Fun, invFun := g18InvFun, left_inv := by decide, right_inv := by decide }

@[expose] def g19Fun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 12, 21, 18, 20, 19, 10, 15, 5, 17, 22, 11, 16, 13, 7, 9, 8, 6, 14]
@[expose] def g19InvFun : Fin 23 → Fin 23 :=
  ![0, 1, 2, 3, 4, 12, 21, 18, 20, 19, 10, 15, 5, 17, 22, 11, 16, 13, 7, 9, 8, 6, 14]
@[expose] def g19 : Perm23 :=
  { toFun := g19Fun, invFun := g19InvFun, left_inv := by decide, right_inv := by decide }

lemma g16_eq_word : g16 = g16Word := by
  ext x
  fin_cases x <;> decide
lemma g17_eq_word : g17 = g17Word := by
  ext x
  fin_cases x <;> decide
lemma g18_eq_word : g18 = g18Word := by
  ext x
  fin_cases x <;> decide
lemma g19_eq_word : g19 = g19Word := by
  ext x
  fin_cases x <;> decide

@[expose] def h5Gen : Fin 4 → Perm23 := ![g16, g17, g18, g19]

@[expose] def M23Gen : Subgroup Perm23 := Subgroup.closure ({a, b} : Set Perm23)

@[expose] abbrev H0 := M23Gen
@[expose] abbrev H1 : Subgroup H0 := MulAction.stabilizer H0 (0 : Fin 23)
@[expose] abbrev H2 : Subgroup H1 := MulAction.stabilizer H1 (1 : Fin 23)
@[expose] abbrev H3 : Subgroup H2 := MulAction.stabilizer H2 (2 : Fin 23)
@[expose] abbrev H4 : Subgroup H3 := MulAction.stabilizer H3 (3 : Fin 23)
@[expose] abbrev H5 : Subgroup H4 := MulAction.stabilizer H4 (4 : Fin 23)
@[expose] abbrev H6 : Subgroup H5 := MulAction.stabilizer H5 (5 : Fin 23)

instance instMulActionH1 : MulAction H1 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H1)
instance instMulActionH2 : MulAction H2 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H2)
instance instMulActionH3 : MulAction H3 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H3)
instance instMulActionH4 : MulAction H4 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H4)
instance instMulActionH5 : MulAction H5 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H5)
instance instMulActionH6 : MulAction H6 (Fin 23) := Subgroup.instMulActionSubtypeMem (S := H6)

instance instSMulH0 : SMul H0 (Fin 23) := (Subgroup.instMulActionSubtypeMem (S := H0)).toSMul
instance instSMulH1 : SMul H1 (Fin 23) := instMulActionH1.toSMul
instance instSMulH2 : SMul H2 (Fin 23) := instMulActionH2.toSMul
instance instSMulH3 : SMul H3 (Fin 23) := instMulActionH3.toSMul
instance instSMulH4 : SMul H4 (Fin 23) := instMulActionH4.toSMul
instance instSMulH5 : SMul H5 (Fin 23) := instMulActionH5.toSMul
instance instSMulH6 : SMul H6 (Fin 23) := instMulActionH6.toSMul

lemma baseGen_mem (i : Fin 2) : baseGen i ∈ M23Gen := by
  fin_cases i
  · change a ∈ M23Gen
    exact Subgroup.subset_closure (by simp)
  · change b ∈ M23Gen
    exact Subgroup.subset_closure (by simp)

lemma g2_mem : g2 ∈ M23Gen := by
  rw [g2_eq_word]
  have hle : Subgroup.closure (Set.range baseGen) ≤ M23Gen := by
    apply (Subgroup.closure_le M23Gen).2
    rintro x ⟨i, rfl⟩
    exact baseGen_mem i
  exact hle (evalGroupWord_mem_closure baseGen _)

lemma g3_mem : g3 ∈ M23Gen := by
  rw [g3_eq_word]
  have hle : Subgroup.closure (Set.range baseGen) ≤ M23Gen := by
    apply (Subgroup.closure_le M23Gen).2
    rintro x ⟨i, rfl⟩
    exact baseGen_mem i
  exact hle (evalGroupWord_mem_closure baseGen _)

lemma g4_mem : g4 ∈ M23Gen := by
  rw [g4_eq_word]
  have hle : Subgroup.closure (Set.range baseGen) ≤ M23Gen := by
    apply (Subgroup.closure_le M23Gen).2
    rintro x ⟨i, rfl⟩
    exact baseGen_mem i
  exact hle (evalGroupWord_mem_closure baseGen _)

lemma g5_mem : g5 ∈ M23Gen := by
  rw [g5_eq_word]
  have hle : Subgroup.closure (Set.range baseGen) ≤ M23Gen := by
    apply (Subgroup.closure_le M23Gen).2
    rintro x ⟨i, rfl⟩
    exact baseGen_mem i
  exact hle (evalGroupWord_mem_closure baseGen _)

lemma h1Gen_mem (i : Fin 4) : h1Gen i ∈ M23Gen := by
  fin_cases i <;> simp [h1Gen, g2_mem, g3_mem, g4_mem, g5_mem]

lemma word_mem_of_mem {n : Nat} (S : Fin n → Perm23)
    (hS : ∀ i, S i ∈ M23Gen) (w : List (Fin n × Bool)) :
    word S w ∈ M23Gen := by
  have hle : Subgroup.closure (Set.range S) ≤ M23Gen := by
    apply (Subgroup.closure_le M23Gen).2
    rintro x ⟨i, rfl⟩
    exact hS i
  exact hle (evalGroupWord_mem_closure S w)

lemma g6_mem : g6 ∈ M23Gen := by rw [g6_eq_word]; exact word_mem_of_mem h1Gen h1Gen_mem _
lemma g7_mem : g7 ∈ M23Gen := by rw [g7_eq_word]; exact word_mem_of_mem h1Gen h1Gen_mem _
lemma g8_mem : g8 ∈ M23Gen := by rw [g8_eq_word]; exact word_mem_of_mem h1Gen h1Gen_mem _
lemma g9_mem : g9 ∈ M23Gen := by rw [g9_eq_word]; exact word_mem_of_mem h1Gen h1Gen_mem _
lemma g10_mem : g10 ∈ M23Gen := by rw [g10_eq_word]; exact word_mem_of_mem h1Gen h1Gen_mem _

lemma h2Gen_mem (i : Fin 5) : h2Gen i ∈ M23Gen := by
  fin_cases i <;> simp [h2Gen, g6_mem, g7_mem, g8_mem, g9_mem, g10_mem]

lemma g11_mem : g11 ∈ M23Gen := by rw [g11_eq_word]; exact word_mem_of_mem h2Gen h2Gen_mem _
lemma g12_mem : g12 ∈ M23Gen := by rw [g12_eq_word]; exact word_mem_of_mem h2Gen h2Gen_mem _

lemma h3Gen_mem (i : Fin 2) : h3Gen i ∈ M23Gen := by
  fin_cases i <;> simp [h3Gen, g11_mem, g12_mem]

lemma g13_mem : g13 ∈ M23Gen := by rw [g13_eq_word]; exact word_mem_of_mem h3Gen h3Gen_mem _
lemma g14_mem : g14 ∈ M23Gen := by rw [g14_eq_word]; exact word_mem_of_mem h3Gen h3Gen_mem _
lemma g15_mem : g15 ∈ M23Gen := by rw [g15_eq_word]; exact word_mem_of_mem h3Gen h3Gen_mem _

lemma h4Gen_mem (i : Fin 3) : h4Gen i ∈ M23Gen := by
  fin_cases i <;> simp [h4Gen, g13_mem, g14_mem, g15_mem]

lemma g16_mem : g16 ∈ M23Gen := by rw [g16_eq_word]; exact word_mem_of_mem h4Gen h4Gen_mem _
lemma g17_mem : g17 ∈ M23Gen := by rw [g17_eq_word]; exact word_mem_of_mem h4Gen h4Gen_mem _
lemma g18_mem : g18 ∈ M23Gen := by rw [g18_eq_word]; exact word_mem_of_mem h4Gen h4Gen_mem _
lemma g19_mem : g19 ∈ M23Gen := by rw [g19_eq_word]; exact word_mem_of_mem h4Gen h4Gen_mem _

lemma h5Gen_mem (i : Fin 4) : h5Gen i ∈ M23Gen := by
  fin_cases i <;> simp [h5Gen, g16_mem, g17_mem, g18_mem, g19_mem]

lemma g2_fix0 : g2 0 = 0 := by decide
lemma g3_fix0 : g3 0 = 0 := by decide
lemma g4_fix0 : g4 0 = 0 := by decide
lemma g5_fix0 : g5 0 = 0 := by decide

lemma g6_fix01 : g6 0 = 0 ∧ g6 1 = 1 := by decide
lemma g7_fix01 : g7 0 = 0 ∧ g7 1 = 1 := by decide
lemma g8_fix01 : g8 0 = 0 ∧ g8 1 = 1 := by decide
lemma g9_fix01 : g9 0 = 0 ∧ g9 1 = 1 := by decide
lemma g10_fix01 : g10 0 = 0 ∧ g10 1 = 1 := by decide

lemma g11_fix012 : g11 0 = 0 ∧ g11 1 = 1 ∧ g11 2 = 2 := by decide
lemma g12_fix012 : g12 0 = 0 ∧ g12 1 = 1 ∧ g12 2 = 2 := by decide

lemma g13_fix0123 : g13 0 = 0 ∧ g13 1 = 1 ∧ g13 2 = 2 ∧ g13 3 = 3 := by decide
lemma g14_fix0123 : g14 0 = 0 ∧ g14 1 = 1 ∧ g14 2 = 2 ∧ g14 3 = 3 := by decide
lemma g15_fix0123 : g15 0 = 0 ∧ g15 1 = 1 ∧ g15 2 = 2 ∧ g15 3 = 3 := by decide

lemma g16_fix01234 : g16 0 = 0 ∧ g16 1 = 1 ∧ g16 2 = 2 ∧ g16 3 = 3 ∧ g16 4 = 4 := by decide
lemma g17_fix01234 : g17 0 = 0 ∧ g17 1 = 1 ∧ g17 2 = 2 ∧ g17 3 = 3 ∧ g17 4 = 4 := by decide
lemma g18_fix01234 : g18 0 = 0 ∧ g18 1 = 1 ∧ g18 2 = 2 ∧ g18 3 = 3 ∧ g18 4 = 4 := by decide
lemma g19_fix01234 : g19 0 = 0 ∧ g19 1 = 1 ∧ g19 2 = 2 ∧ g19 3 = 3 ∧ g19 4 = 4 := by decide

@[expose] def T0 : Fin 23 → List (Fin 2 × Bool) :=
  ![
    [], [(0, false)], [(1, true)], [(0, false), (1, true)],
    [(1, false), (0, false), (1, true)],
    [(1, true), (0, false), (1, false), (1, false), (0, false)],
    [(0, false), (1, false), (1, false), (0, false), (1, true)],
    [(1, false), (1, false), (0, false), (1, true)],
    [(1, false), (0, false)], [(0, false), (1, false), (0, false)],
    [(1, false), (1, false)], [(1, true), (0, false)],
    [(0, false), (1, false), (0, false), (1, false), (1, false), (0, false)],
    [(1, false), (0, false), (1, false), (1, false), (0, false)],
    [(0, false), (1, false)], [(1, false)], [(1, false), (0, false), (1, false)],
    [(1, false), (1, false), (0, false), (1, false), (1, false), (0, false)],
    [(0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
      (1, false), (0, false)],
    [(1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false)],
    [(1, false), (1, false), (0, false)], [(0, false), (1, false), (1, false), (0, false)],
    [(1, true), (0, false), (1, true)]
  ]

@[expose] def T1 : Fin 23 → List (Fin 4 × Bool) :=
  ![
    [], [], [(3, true), (2, false), (3, false)], [(1, false), (2, false), (3, false)],
    [(0, false)], [(2, false), (3, true), (2, false)],
    [(3, false), (2, false), (3, false)], [(2, false), (3, false)],
    [(1, false), (0, false), (1, false), (2, false)], [(3, false), (2, false)],
    [(2, false), (3, false), (1, false), (2, false)], [(1, false), (3, false)],
    [(3, true), (2, false)], [(0, false), (1, false), (2, false)],
    [(0, false), (3, false), (2, false)], [(3, false)],
    [(3, false), (1, false), (3, false)], [(2, false)], [(0, false), (2, false)],
    [(1, false), (2, false)], [(3, false), (1, false), (2, false)],
    [(3, false), (2, false), (3, true), (2, false)],
    [(3, true), (1, false), (3, false)]
  ]

@[expose] def T2 : Fin 23 → List (Fin 5 × Bool) :=
  ![
    [], [], [], [(1, false), (0, false)], [(4, false), (3, false), (4, false)],
    [(0, false)], [(1, false)], [(4, false), (3, false)], [(4, false), (0, false)],
    [(3, false)], [(0, false), (1, false)], [(3, false), (0, false)],
    [(1, false), (3, false)], [(0, false), (4, false), (0, false)],
    [(1, false), (3, false), (0, false)], [(3, false), (4, false)], [(4, true)],
    [(4, true), (3, false), (0, false)], [(4, false), (3, false), (0, false)],
    [(2, false), (4, true), (0, false)], [(0, false), (3, false)],
    [(4, true), (0, false)], [(4, false)]
  ]

@[expose] def T3 : Fin 23 → List (Fin 2 × Bool) :=
  ![
    [], [], [], [], [(1, false), (1, false), (0, true)],
    [(1, true), (0, true), (1, false)], [(0, true), (1, false)],
    [(0, false), (1, false)], [(1, false), (0, true), (1, false)],
    [(1, false), (0, true)], [(0, true)], [(0, true), (1, true), (0, true)],
    [(0, false), (1, true), (0, true)],
    [(1, true), (0, true), (1, false), (0, true)],
    [(0, true), (1, false), (0, true)], [(1, true), (0, true)], [(0, false)],
    [(0, false), (1, true)], [(1, false), (0, true), (1, false), (0, true)],
    [(0, true), (1, true)], [(0, false), (1, false), (0, true)], [(1, true)], [(1, false)]
  ]

@[expose] def T4 : Fin 23 → List (Fin 3 × Bool) :=
  ![[], [], [], [], [], [], [], [], [], [], [(0, false)], [], [], [], [], [],
    [(0, true)], [], [], [], [], [], []]

@[expose] def T5 : Fin 23 → List (Fin 4 × Bool) :=
  ![
    [], [], [], [], [], [], [(2, false), (1, false)],
    [(2, false), (1, false), (0, false)], [(2, false), (0, false)], [(2, false)], [],
    [(1, false), (0, false)], [(3, false)], [(3, false), (1, false)],
    [(3, false), (0, false)], [(3, false), (1, false), (0, false)], [],
    [(1, false)], [(3, false), (2, false), (1, false), (0, false)],
    [(3, false), (2, false)], [(3, false), (2, false), (0, false)],
    [(3, false), (2, false), (1, false)], [(0, false)]
  ]

lemma T0_eval (x : Fin 23) : word baseGen (T0 x) 0 = x := by
  fin_cases x <;> decide

lemma T1_eval (x : Fin 23) (hx : x ≠ 0) : word h1Gen (T1 x) 1 = x := by
  fin_cases x <;> simp_all <;> decide

lemma T2_eval (x : Fin 23) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    word h2Gen (T2 x) 2 = x := by
  fin_cases x <;> simp_all <;> decide

lemma T3_eval (x : Fin 23) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    word h3Gen (T3 x) 3 = x := by
  fin_cases x <;> simp_all <;> decide

lemma T4_eval (x : Fin 23) (hx : x = 4 ∨ x = 10 ∨ x = 16) :
    word h4Gen (T4 x) 4 = x := by
  rcases hx with rfl | rfl | rfl <;> decide

lemma T5_eval (x : Fin 23)
    (hx : x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 11 ∨ x = 12 ∨
      x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 17 ∨ x = 18 ∨ x = 19 ∨ x = 20 ∨
      x = 21 ∨ x = 22) :
    word h5Gen (T5 x) 5 = x := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[expose] def E0 : Fin 23 → Fin 2 → List (Fin 4 × Bool) := ![
  ![[], []],
  ![[], []],
  ![[], []],
  ![[], []],
  ![[(0, false), (1, false), (2, false), (3, false), (2, false), (3, true), (1, false), (3, false), (2, false), (3, true), (2, false), (1, false)], []],
  ![[(2, false), (0, false), (3, true), (0, false), (2, false), (0, false), (3, false), (2, false)], []],
  ![[], [(3, false), (3, false), (1, false), (0, false), (3, false), (0, false), (1, false), (3, false), (3, false)]],
  ![[], []],
  ![[], []],
  ![[], [(3, false)]],
  ![[(2, false)], []],
  ![[(0, false)], []],
  ![[], []],
  ![[], []],
  ![[], []],
  ![[], []],
  ![[(0, false), (3, true), (1, false), (3, true), (0, false), (1, false), (3, false), (1, false), (3, true), (2, false), (0, false), (3, true)], [(1, false)]],
  ![[(2, false)], []],
  ![[], [(2, false), (3, false), (1, false), (2, false), (0, false), (3, false), (2, false), (3, false), (1, false), (2, false)]],
  ![[], [(1, false), (0, false), (3, true), (0, false), (2, false), (1, false), (2, false), (3, false), (0, false), (1, false), (2, false)]],
  ![[], []],
  ![[], []],
  ![[(2, false), (1, false), (2, false), (3, true), (2, false), (1, false), (3, false), (2, false), (3, false)], []]
]
@[expose] def E1 : Fin 23 → Fin 4 → List (Fin 5 × Bool) := ![
  ![[], [], [], []],
  ![[], [(0, false)], [], []],
  ![[(4, true), (3, false), (4, false)], [(2, false), (3, false), (4, false), (0, false), (4, true), (0, false)], [(1, false), (3, false), (4, false), (0, false), (2, false), (4, false), (0, false), (2, false)], []],
  ![[(4, false), (3, false), (4, false), (3, false), (4, true), (3, false), (4, true)], [], [(4, false), (0, false), (3, false), (2, false), (4, true), (3, false), (4, true)], [(0, false), (4, false), (2, false), (0, false), (4, true), (2, false), (4, true), (3, false), (4, true)]],
  ![[], [(2, false)], [(3, false)], [(4, false)]],
  ![[(0, false), (4, false), (2, false), (3, false), (0, false), (4, false), (0, false), (4, false)], [(0, false), (4, false), (0, false), (4, true), (3, false), (2, false)], [], []],
  ![[(4, true), (3, false), (4, false)], [(4, false), (0, false), (4, false), (0, false), (4, true), (0, false), (1, false), (3, false)], [(4, false), (3, false), (4, false), (2, false), (3, false), (0, false), (4, true)], [(0, false), (4, false), (0, false), (2, false), (0, false), (4, true)]],
  ![[(0, false), (1, false), (3, false), (4, false), (0, false), (1, false), (2, false)], [], [], []],
  ![[(2, false), (0, false), (4, true), (0, false), (4, true), (0, false), (3, false)], [], [(0, false), (2, false), (3, false), (2, false), (0, false)], [(0, false), (4, false), (3, false), (4, false), (0, false), (3, false), (4, false), (2, false)]],
  ![[], [(0, false), (4, false), (0, false), (4, true), (0, false), (3, false)], [(0, false), (3, false), (4, true), (3, false), (2, false), (4, false)], [(1, false), (3, false), (1, false)]],
  ![[(1, false), (3, false), (4, true), (2, false), (4, false), (0, false), (4, false)], [(3, false), (1, false), (0, false), (4, false), (0, false), (4, true), (0, false), (4, true)], [], [(4, false), (0, false), (2, false), (0, false), (4, true), (0, false)]],
  ![[(4, false), (3, false), (2, false), (3, false), (0, false), (4, false), (2, false), (1, false)], [], [(2, false), (4, true), (2, false), (3, false), (4, false), (3, false)], []],
  ![[(1, false), (2, false), (4, false), (0, false), (1, false), (3, false), (0, false), (4, false)], [(3, false), (0, false), (4, true), (0, false), (4, false), (0, false), (3, false)], [], []],
  ![[], [], [(0, false), (1, false), (3, false), (1, false), (0, false)], [(0, false), (2, false), (0, false), (3, false), (2, false), (4, false), (0, false)]],
  ![[], [(1, false), (0, false), (4, true), (0, false), (4, true), (0, false), (3, false), (1, false)], [(2, false), (0, false), (1, false), (3, false), (4, false), (0, false), (2, false), (4, false)], [(1, false), (2, false), (4, false), (0, false), (1, false), (3, false), (0, false), (4, false)]],
  ![[(0, false), (3, false), (4, false), (2, false), (0, false), (4, true), (0, false), (4, false)], [], [], [(1, false)]],
  ![[(4, true), (0, false), (4, true), (2, false), (4, false), (3, false), (1, false)], [(1, false), (0, false)], [(0, false), (1, false), (3, false), (0, false), (4, false), (0, false), (4, true), (0, false), (1, false)], [(4, false), (3, false), (2, false), (3, false), (0, false), (4, false), (2, false), (1, false)]],
  ![[], [], [], []],
  ![[], [(0, false), (1, false), (0, false), (2, false)], [(0, false), (3, false), (1, false)], [(1, false), (3, false), (1, false)]],
  ![[], [], [(1, false), (3, false), (0, false)], []],
  ![[(0, false), (4, false), (0, false), (4, false), (3, false), (2, false), (4, true), (3, false), (1, false)], [(3, false), (0, false), (4, false), (0, false), (4, true), (0, false)], [], [(0, false), (1, false), (0, false)]],
  ![[(0, false), (4, true), (0, false), (4, true), (0, false), (3, false), (2, false)], [(0, false), (3, false), (2, false), (0, false), (4, false), (2, false), (4, true), (3, false), (4, false)], [(0, false), (3, false), (4, false), (2, false), (0, false), (4, true), (0, false), (1, false)], [(0, false), (3, false), (4, true), (3, false), (2, false), (4, false)]],
  ![[(2, false), (1, false), (0, false), (4, true), (3, false), (1, false), (0, false)], [(0, false), (1, false)], [(2, false), (1, false), (3, false), (4, false), (0, false), (4, true)], []]
]
@[expose] def E2 : Fin 23 → Fin 5 → List (Fin 2 × Bool) := ![
  ![[], [], [], [], []],
  ![[], [], [], [], []],
  ![[], [], [(0, false)], [], []],
  ![[(1, false), (0, false), (1, false), (1, false), (0, true)], [], [(1, false), (0, true)], [(0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], []],
  ![[(1, false), (0, false), (1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false)], [(1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false)], [(0, false), (1, false), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false), (0, false), (1, true)], [(1, false), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false)], [(1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false)]],
  ![[], [], [(0, true)], [], []],
  ![[], [], [(1, false)], [(1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (1, false)], []],
  ![[(0, false), (1, false), (1, false), (0, true), (1, true)], [(0, false), (1, false), (1, false), (0, true), (1, true)], [(1, false), (1, false), (0, false), (1, false)], [(0, true), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false)], []],
  ![[], [], [(0, false), (1, false), (1, false), (0, true)], [(0, false), (1, false), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false), (0, false), (1, false)], []],
  ![[], [], [(0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false)], [], []],
  ![[], [(1, false), (0, false), (1, false), (1, false), (0, true)], [(1, true), (0, true), (1, false), (1, false)], [(0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false)], [(1, false), (0, false), (1, false), (1, false), (0, true)]],
  ![[(1, false)], [], [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], [], []],
  ![[(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], [], [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false), (0, false)], [(1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (1, false)], [(0, false), (1, false), (1, false), (0, true), (1, true)]],
  ![[], [(1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false)], [(0, false), (1, true), (0, true), (1, false), (0, true)], [(0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (1, false)], [(0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (1, true)]],
  ![[(0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false)], [], [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], [(0, false), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], []],
  ![[(1, true)], [(1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false)], [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false)], [], []],
  ![[(1, false), (0, false), (1, true)], [], [(1, true)], [(0, false), (1, true)], []],
  ![[(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, true)], [], [(0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, false)], [(1, false), (1, false), (0, true), (1, true), (0, false), (1, true), (0, true)], []],
  ![[(0, false), (1, false), (0, false), (1, false), (1, false), (0, true), (1, false), (0, true)], [], [(0, false), (1, true), (0, false), (1, false), (0, true)], [(0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (1, false)], []],
  ![[(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, true)], [(0, false), (1, false), (1, false), (0, true)], [], [(0, false), (1, false), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false), (0, false), (1, true)], [(0, false), (1, false), (0, true)]],
  ![[], [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false)], [(1, false), (0, true)], [(0, false), (1, false), (0, true), (1, false), (0, true)]],
  ![[(1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false)], [], [], [(1, false), (1, false)], []],
  ![[(1, false), (0, true), (1, true)], [], [(0, false), (1, true)], [], []]
]
@[expose] def E3 : Fin 23 → Fin 2 → List (Fin 3 × Bool) := ![
  ![[], []],
  ![[], []],
  ![[], []],
  ![[], []],
  ![[(0, false)], []],
  ![[(0, false), (1, true), (2, true)], []],
  ![[], []],
  ![[], [(1, false)]],
  ![[(0, true), (2, false)], [(1, true), (2, false)]],
  ![[], []],
  ![[], []],
  ![[], [(1, false), (2, true)]],
  ![[], [(2, true)]],
  ![[(1, false), (2, false)], []],
  ![[], []],
  ![[], []],
  ![[], [(0, false)]],
  ![[], [(1, true), (2, true)]],
  ![[(0, true), (1, true)], [(1, false), (2, true)]],
  ![[], [(1, true), (2, false)]],
  ![[], [(1, false), (2, false)]],
  ![[], []],
  ![[], [(0, true)]]
]
@[expose] def E4 : Fin 23 → Fin 3 → List (Fin 4 × Bool) := ![
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [(0, false)], [(2, false)]],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [(0, false), (1, false)], [(2, false), (3, false)]],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [(1, false)], [(3, false)]],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []],
  ![[], [], []]
]

end M23.M23Group

end CFSG
