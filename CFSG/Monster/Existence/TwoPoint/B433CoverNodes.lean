module

public import CFSG.Certificates.CosetEnumeration
public import CFSG.Monster.Existence.TwoPoint.B433CoverData
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

variable {G H : Type*} [Group G] [Group H]

theorem evalWord_append (gen : ℕ → G) (u v : List ℕ) :
    evalWord gen (u ++ v) = evalWord gen u * evalWord gen v := by
  simp [evalWord]

theorem evalWord_inv_of_involutive (gen : ℕ → G) {w : List ℕ}
    (hw : ∀ l ∈ w, gen l * gen l = 1) : (evalWord gen w)⁻¹ = evalWord gen w.reverse := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha : gen a * gen a = 1 := hw a List.mem_cons_self
    have hw' : ∀ l ∈ w, gen l * gen l = 1 := fun l hl => hw l (List.mem_cons_of_mem _ hl)
    rw [evalWord_cons, mul_inv_rev, ih hw', List.reverse_cons, evalWord_append]
    simp only [evalWord_cons, evalWord_nil, mul_one, inv_eq_of_mul_eq_one_right ha]

theorem evalWord_congr {gen gen' : ℕ → G} {w : List ℕ} (h : ∀ l ∈ w, gen l = gen' l) :
    evalWord gen w = evalWord gen' w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [evalWord_cons, evalWord_cons, h a List.mem_cons_self,
      ih fun l hl => h l (List.mem_cons_of_mem _ hl)]

theorem map_evalWord (f : G →* H) (gen : ℕ → G) (w : List ℕ) :
    f (evalWord gen w) = evalWord (fun l => f (gen l)) w := by
  induction w with
  | nil => simp
  | cons a w ih => rw [evalWord_cons, evalWord_cons, map_mul, ih]

@[expose] def nodeConj (gen : ℕ → G) (t : G) (j : ℕ) : G :=
  evalWord gen (nodeWord j) * t * (evalWord gen (nodeWord j))⁻¹

@[expose] noncomputable def nodeProd (gen : ℕ → G) (t : G) (j : ℕ) : G :=
  if _h : 0 < j ∧ j < 23 then nodeProd gen t (nodeParent j) * nodeConj gen t j else 1
termination_by j
decreasing_by exact nodeParent_lt j _h.2 _h.1

theorem nodeProd_zero (gen : ℕ → G) (t : G) : nodeProd gen t 0 = 1 := by
  rw [nodeProd]
  simp

theorem nodeProd_eq (gen : ℕ → G) (t : G) {j : ℕ} (hj : 0 < j) (hj' : j < 23) :
    nodeProd gen t j =
      nodeProd gen t (nodeParent j) *
        (evalWord gen (nodeWord j) * t * (evalWord gen (nodeWord j))⁻¹) := by
  rw [nodeProd]
  simp [hj, hj', nodeConj]

theorem nodeProd_one (gen : ℕ → G) (t : G) : nodeProd gen t 1 = t := by
  rw [nodeProd_eq gen t (by norm_num) (by norm_num), nodeParent_one, nodeProd_zero, nodeWord_one]
  simp

theorem nodeProd_of_not (gen : ℕ → G) (t : G) {j : ℕ} (hj : ¬(0 < j ∧ j < 23)) :
    nodeProd gen t j = 1 := by
  rw [nodeProd]
  exact dite_eq_right hj

theorem nodeProd_of_ge (gen : ℕ → G) (t : G) {j : ℕ} (hj : 23 ≤ j) : nodeProd gen t j = 1 :=
  nodeProd_of_not gen t fun h => absurd h.2 (not_lt.2 hj)

theorem nodeProd_map (f : G →* H) (gen : ℕ → G) (t : G) (j : ℕ) :
    f (nodeProd gen t j) = nodeProd (fun l => f (gen l)) (f t) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : 0 < j ∧ j < 23
    · rw [nodeProd_eq gen t hj.1 hj.2, nodeProd_eq _ _ hj.1 hj.2, map_mul, map_mul, map_mul,
        map_inv, map_evalWord, ih _ (nodeParent_lt j hj.2 hj.1)]
    · rw [nodeProd_of_not gen t hj, nodeProd_of_not _ _ hj, map_one]

theorem nodeProd_congr {gen gen' : ℕ → G} (h : ∀ l < 10, gen l = gen' l) (t : G) (j : ℕ) :
    nodeProd gen t j = nodeProd gen' t j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : 0 < j ∧ j < 23
    · rw [nodeProd_eq gen t hj.1 hj.2, nodeProd_eq gen' t hj.1 hj.2,
        ih _ (nodeParent_lt j hj.2 hj.1),
        evalWord_congr (gen := gen) (gen' := gen') fun l hl => h l (nodeWord_lt j hj.2 l hl)]
    · rw [nodeProd_of_not gen t hj, nodeProd_of_not gen' t hj]

@[expose] def nodeLetters (j : ℕ) : List ℕ :=
  if _h : 0 < j ∧ j < 23 then
    nodeLetters (nodeParent j) ++ (nodeWord j ++ 10 :: (nodeWord j).reverse)
  else []
termination_by j
decreasing_by exact nodeParent_lt j _h.2 _h.1

theorem nodeLetters_of_not {j : ℕ} (hj : ¬(0 < j ∧ j < 23)) : nodeLetters j = [] := by
  rw [nodeLetters]
  exact dite_eq_right hj

theorem nodeLetters_zero : nodeLetters 0 = [] :=
  nodeLetters_of_not fun h => absurd h.1 (lt_irrefl 0)

theorem nodeLetters_eq {j : ℕ} (hj : 0 < j) (hj' : j < 23) :
    nodeLetters j = nodeLetters (nodeParent j) ++ (nodeWord j ++ 10 :: (nodeWord j).reverse) := by
  rw [nodeLetters]
  simp [hj, hj']

theorem nodeLetters_one : nodeLetters 1 = [10] := by
  rw [nodeLetters_eq (by norm_num) (by norm_num), nodeParent_one, nodeLetters_zero, nodeWord_one]
  rfl

theorem nodeLetters_le (j : ℕ) : ∀ l ∈ nodeLetters j, l ≤ 10 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : 0 < j ∧ j < 23
    · rw [nodeLetters_eq hj.1 hj.2]
      intro l hl
      simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hl
      rcases hl with hl | hl | rfl | hl
      · exact ih _ (nodeParent_lt j hj.2 hj.1) l hl
      · exact (nodeWord_lt j hj.2 l hl).le.trans (by norm_num)
      · exact le_rfl
      · exact (nodeWord_lt j hj.2 l hl).le.trans (by norm_num)
    · rw [nodeLetters_of_not hj]
      simp

theorem nodeProd_eq_evalWord {gen : ℕ → G} {t : G} (ht : gen 10 = t)
    (hinv : ∀ l < 10, gen l * gen l = 1) (j : ℕ) :
    nodeProd gen t j = evalWord gen (nodeLetters j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : 0 < j ∧ j < 23
    · rw [nodeProd_eq gen t hj.1 hj.2, nodeLetters_eq hj.1 hj.2, evalWord_append,
        ih _ (nodeParent_lt j hj.2 hj.1), evalWord_append, evalWord_cons, ht,
        evalWord_inv_of_involutive gen fun l hl => hinv l (nodeWord_lt j hj.2 l hl)]
      simp only [mul_assoc]
    · rw [nodeProd_of_not gen t hj, nodeLetters_of_not hj]
      rfl

end CFSG.Monster.Existence.B433Cover
