module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.ComponentInitial (altThreeCyclePerm closure_altThreeCyclePerm)

theorem list_prod_mem_closure {G : Type*} [Group G] {r : ℕ} (f : Fin r → G) (w : List (Fin r)) :
    (w.map f).prod ∈ closure (Set.range f) := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih => exact mul_mem (subset_closure ⟨i, rfl⟩) ih

theorem alternatingGroup_le_closure {m r : ℕ} (f : Fin r → Perm (Fin (m + 2)))
    (w : Fin m → List (Fin r)) (hw : ∀ i, altThreeCyclePerm i = ((w i).map f).prod) :
    alternatingGroup (Fin (m + 2)) ≤ closure (Set.range f) := by
  rw [← closure_altThreeCyclePerm, closure_le]
  rintro _ ⟨i, rfl⟩
  rw [hw i]
  exact list_prod_mem_closure f (w i)

@[expose] def gens7 : Fin 6 → Perm (Fin 7) :=
  ![swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5, swap 0 1 * swap 2 6,
    swap 0 2 * swap 1 6, swap 0 6 * swap 1 2]

@[expose] def words7 : Fin 5 → List (Fin 6) :=
  ![[0, 3, 0, 4, 0, 5, 0, 3], [4, 2, 3, 2, 5], [4, 1, 3, 1, 5], [4, 0, 3, 0, 5],
    [0, 4, 0, 3, 0, 5, 0]]

theorem gens7_words : ∀ i : Fin 5, altThreeCyclePerm i = ((words7 i).map gens7).prod := by
  decide +kernel

theorem closure_gens7 : alternatingGroup (Fin 7) ≤ closure (Set.range gens7) :=
  alternatingGroup_le_closure (m := 5) gens7 words7 gens7_words

theorem gens7_spec : ∀ i : Fin 6, sign (gens7 i) = 1 ∧ gens7 i ^ 2 = 1 ∧
    ((i : ℕ) < 3 → gens7 i * c1 7 = c1 7 * gens7 i) ∧
    (3 ≤ (i : ℕ) → gens7 i * c2 7 = c2 7 * gens7 i) := by
  decide +kernel

@[expose] def gens8 : Fin 6 → Perm (Fin 8) :=
  ![swap 3 4 * swap 6 7, swap 4 5 * swap 6 7, swap 3 6 * swap 4 7, swap 0 1 * swap 6 7,
    swap 1 2 * swap 6 7, swap 0 6 * swap 1 7]

@[expose] def words8 : Fin 6 → List (Fin 6) :=
  ![[3, 4], [2, 3, 4, 3, 5, 4, 5, 4, 2], [1, 5, 0, 2, 1, 2, 5, 1], [5, 0, 2, 1, 2, 5],
    [3, 4, 3, 5, 4, 5, 4], [3, 4, 5, 4, 3, 5, 4]]

theorem gens8_words : ∀ i : Fin 6, altThreeCyclePerm i = ((words8 i).map gens8).prod := by
  decide +kernel

theorem closure_gens8 : alternatingGroup (Fin 8) ≤ closure (Set.range gens8) :=
  alternatingGroup_le_closure (m := 6) gens8 words8 gens8_words

theorem gens8_spec : ∀ i : Fin 6, sign (gens8 i) = 1 ∧ gens8 i ^ 2 = 1 ∧
    ((i : ℕ) < 3 → gens8 i * c1 8 = c1 8 * gens8 i) ∧
    (3 ≤ (i : ℕ) → gens8 i * c2 8 = c2 8 * gens8 i) := by
  decide +kernel

@[expose] def gens10 : Fin 6 → Perm (Fin 10) :=
  ![swap 6 7 * swap 8 9, swap 6 8 * swap 7 9, swap 3 4 * swap 5 9, swap 3 5 * swap 4 9,
    swap 0 1 * swap 2 9, swap 0 2 * swap 1 9]

@[expose] def words10 : Fin 8 → List (Fin 6) :=
  ![[0, 4, 0, 5, 0, 4, 5, 0, 4], [2, 5, 3, 4, 3, 4, 5, 2], [5, 3, 4, 3, 4, 5],
    [5, 2, 4, 2, 4, 5], [0, 5, 1, 4, 1, 4, 5, 0], [5, 1, 4, 1, 4, 5], [5, 0, 4, 0, 4, 5],
    [0, 5, 0, 4, 0, 4, 5, 0]]

theorem gens10_words : ∀ i : Fin 8, altThreeCyclePerm i = ((words10 i).map gens10).prod := by
  decide +kernel

theorem closure_gens10 : alternatingGroup (Fin 10) ≤ closure (Set.range gens10) :=
  alternatingGroup_le_closure (m := 8) gens10 words10 gens10_words

theorem gens10_spec : ∀ i : Fin 6, sign (gens10 i) = 1 ∧ gens10 i ^ 2 = 1 ∧
    ((i : ℕ) < 2 → gens10 i * c1 10 = c1 10 * gens10 i ∧ gens10 i * c2 10 = c2 10 * gens10 i) ∧
    (2 ≤ (i : ℕ) → (i : ℕ) < 4 →
      gens10 i * c1 10 = c1 10 * gens10 i ∧ gens10 i * c3 10 = c3 10 * gens10 i) ∧
    (4 ≤ (i : ℕ) → gens10 i * c2 10 = c2 10 * gens10 i ∧ gens10 i * c3 10 = c3 10 * gens10 i) := by
  decide +kernel

@[expose] def gens11 : Fin 6 → Perm (Fin 11) :=
  ![swap 6 7 * swap 8 9, swap 7 8 * swap 9 10, swap 3 4 * swap 5 9, swap 4 5 * swap 9 10,
    swap 0 1 * swap 2 9, swap 1 2 * swap 9 10]

@[expose] def words11 : Fin 9 → List (Fin 6) :=
  ![[4, 1, 4, 1, 4, 5], [2, 3, 2, 4, 5, 4, 2, 3, 4, 2], [3, 2, 4, 5, 4, 2, 3, 4],
    [1, 2, 4, 5, 4, 2, 1, 4], [0, 1, 0, 4, 5, 4, 0, 1, 4, 0], [1, 0, 4, 5, 4, 0, 1, 4],
    [0, 4, 5, 4, 0, 1, 4, 1], [4, 5, 4, 1, 4, 1], [1, 4, 5, 4, 1, 4]]

theorem gens11_words : ∀ i : Fin 9, altThreeCyclePerm i = ((words11 i).map gens11).prod := by
  decide +kernel

theorem closure_gens11 : alternatingGroup (Fin 11) ≤ closure (Set.range gens11) :=
  alternatingGroup_le_closure (m := 9) gens11 words11 gens11_words

theorem gens11_spec : ∀ i : Fin 6, sign (gens11 i) = 1 ∧ gens11 i ^ 2 = 1 ∧
    ((i : ℕ) < 2 → gens11 i * c1 11 = c1 11 * gens11 i ∧ gens11 i * c2 11 = c2 11 * gens11 i) ∧
    (2 ≤ (i : ℕ) → (i : ℕ) < 4 →
      gens11 i * c1 11 = c1 11 * gens11 i ∧ gens11 i * c3 11 = c3 11 * gens11 i) ∧
    (4 ≤ (i : ℕ) → gens11 i * c2 11 = c2 11 * gens11 i ∧ gens11 i * c3 11 = c3 11 * gens11 i) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
