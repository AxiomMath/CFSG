module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

namespace RootLineAux

open Matrix

def sA {n : ℕ} (x y : Coords n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0

def sB {n : ℕ} (x y : Coords n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = 0 ∧ y i ≠ 0

def sC {n : ℕ} (x y : Coords n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = y i ∧ x i ≠ 0

def sD {n : ℕ} (x y : Coords n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = -y i ∧ x i ≠ 0

private lemma ind_add (a b : ZMod 3) :
    (if a + b ≠ 0 then (1 : ℕ) else 0) =
      (if a ≠ 0 ∧ b = 0 then 1 else 0) + (if a = 0 ∧ b ≠ 0 then 1 else 0) +
        (if a = b ∧ a ≠ 0 then 1 else 0) := by
  revert a b
  decide

private lemma ind_sub (a b : ZMod 3) :
    (if a - b ≠ 0 then (1 : ℕ) else 0) =
      (if a ≠ 0 ∧ b = 0 then 1 else 0) + (if a = 0 ∧ b ≠ 0 then 1 else 0) +
        (if a = -b ∧ a ≠ 0 then 1 else 0) := by
  revert a b
  decide

private lemma ind_left (a b : ZMod 3) :
    (if a ≠ 0 then (1 : ℕ) else 0) =
      (if a ≠ 0 ∧ b = 0 then 1 else 0) + (if a = b ∧ a ≠ 0 then 1 else 0) +
        (if a = -b ∧ a ≠ 0 then 1 else 0) := by
  revert a b
  decide

private lemma ind_right (a b : ZMod 3) :
    (if b ≠ 0 then (1 : ℕ) else 0) =
      (if a = 0 ∧ b ≠ 0 then 1 else 0) + (if a = b ∧ a ≠ 0 then 1 else 0) +
        (if a = -b ∧ a ≠ 0 then 1 else 0) := by
  revert a b
  decide

private lemma wt_eq_sum_ind {n : ℕ} (e : Coords n) :
    wt e = ∑ i : Fin n, if e i ≠ 0 then (1 : ℕ) else 0 := by
  rw [wt]
  exact (Finset.sum_boole (fun i => e i ≠ 0) Finset.univ).symm

private lemma card_eq_sum_ind {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i : Fin n, if p i then (1 : ℕ) else 0 := by
  exact (Finset.sum_boole p Finset.univ).symm

lemma wt_add_eq {n : ℕ} (x y : Coords n) :
    wt (x + y) = (sA x y).card + (sB x y).card + (sC x y).card := by
  rw [wt_eq_sum_ind]
  simp only [sA, sB, sC, sD]
  rw [card_eq_sum_ind (fun i => x i ≠ 0 ∧ y i = 0),
    card_eq_sum_ind (fun i => x i = 0 ∧ y i ≠ 0),
    card_eq_sum_ind (fun i => x i = y i ∧ x i ≠ 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using ind_add (x i) (y i)

lemma wt_sub_eq {n : ℕ} (x y : Coords n) :
    wt (x - y) = (sA x y).card + (sB x y).card + (sD x y).card := by
  rw [wt_eq_sum_ind]
  simp only [sA, sB, sC, sD]
  rw [card_eq_sum_ind (fun i => x i ≠ 0 ∧ y i = 0),
    card_eq_sum_ind (fun i => x i = 0 ∧ y i ≠ 0),
    card_eq_sum_ind (fun i => x i = -y i ∧ x i ≠ 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using ind_sub (x i) (y i)

lemma wt_left_eq {n : ℕ} (x y : Coords n) :
    wt x = (sA x y).card + (sC x y).card + (sD x y).card := by
  rw [wt_eq_sum_ind]
  simp only [sA, sB, sC, sD]
  rw [card_eq_sum_ind (fun i => x i ≠ 0 ∧ y i = 0),
    card_eq_sum_ind (fun i => x i = y i ∧ x i ≠ 0),
    card_eq_sum_ind (fun i => x i = -y i ∧ x i ≠ 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using ind_left (x i) (y i)

lemma wt_right_eq {n : ℕ} (x y : Coords n) :
    wt y = (sB x y).card + (sC x y).card + (sD x y).card := by
  rw [wt_eq_sum_ind]
  simp only [sA, sB, sC, sD]
  rw [card_eq_sum_ind (fun i => x i = 0 ∧ y i ≠ 0),
    card_eq_sum_ind (fun i => x i = y i ∧ x i ≠ 0),
    card_eq_sum_ind (fun i => x i = -y i ∧ x i ≠ 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using ind_right (x i) (y i)

private lemma eq_or_eq_neg_of_ne_zero (a b : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ∨ a = -b := by
  revert a b
  decide

lemma support_disjoint_of_empty_CD {n : ℕ} {x y : Coords n}
    (hC : ∀ i, i ∉ sC x y) (hD : ∀ i, i ∉ sD x y) :
    ∀ i, x i = 0 ∨ y i = 0 := by
  intro i
  by_cases hx : x i = 0
  · exact Or.inl hx
  · right
    by_contra hy
    have hmem : i ∈ sC x y ∨ i ∈ sD x y := by
      rcases eq_or_eq_neg_of_ne_zero (x i) (y i) hx hy with h | h
      · left
        simp only [sC, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, hx⟩
      · right
        simp only [sD, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, hx⟩
    rcases hmem with h | h
    · exact hC i h
    · exact hD i h

lemma support_eq_of_empty_AB {n : ℕ} {x y : Coords n}
    (hA : ∀ i, i ∉ sA x y) (hB : ∀ i, i ∉ sB x y) :
    ∀ i, x i = 0 ↔ y i = 0 := by
  intro i
  constructor
  · intro hx
    by_contra hy
    exact hB i (by
      simp only [sB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx, hy⟩)
  · intro hy
    by_contra hx
    exact hA i (by
      simp only [sA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx, hy⟩)

lemma wt_eq_zero_iff {n : ℕ} {e : Coords n} : wt e = 0 ↔ e = 0 := by
  rw [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hi
    exact h (Finset.mem_univ i) hi
  · intro h
    subst h
    simp

lemma eq_one_or_eq_neg_one_of_ne_zero (a : ZMod 3) (h : a ≠ 0) :
    a = 1 ∨ a = -1 :=
  eq_or_eq_neg_of_ne_zero a 1 h one_ne_zero

lemma mulVec_cons_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
    (hA : ∀ j : Fin n, M 0 j.succ = 0) (v : Fin n → ZMod 3) :
    M *ᵥ Fin.cons 0 v = Fin.cons 0 ((M.submatrix Fin.succ Fin.succ) *ᵥ v) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hA]
  | succ k =>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hA]

lemma wt_cons_zero {n : ℕ} (v : Fin n → ZMod 3) :
    wt (Fin.cons 0 v) = wt v := by
  rw [wt_eq_sum_ind, wt_eq_sum_ind, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

lemma single_succ {n : ℕ} (i : Fin n) (x : ZMod 3) (k : Fin n) :
    (Pi.single i.succ x : Fin (n + 1) → ZMod 3) k.succ =
      (Pi.single i x : Fin n → ZMod 3) k := by
  by_cases h : k = i
  · subst h
    simp
  · have h' : k.succ ≠ i.succ := fun hh => h (Fin.succ_inj.mp hh)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

end RootLineAux

end CFSG.StandardType.FrameRoute.FS81
