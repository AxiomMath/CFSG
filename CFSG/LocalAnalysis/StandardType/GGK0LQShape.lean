module

public import CFSG.LocalAnalysis.StandardType.GGK0LQExt
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGKacCompsSpec
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley

@[expose] def lqShapeCount : LargeEvenLieTag × ℕ → ℕ
  | (.A, r) => r * (r + 1)
  | (.C, r) => 2 * (r * r)
  | (.D, r) => 2 * (r * (r - 1))
  | (.E6, _) => 72
  | (.E7, _) => 126
  | (.E8, _) => 240
  | (.F4, _) => 48
  | (.G2, _) => 12
  | _ => 0

private theorem lk0xlqshape_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private theorem lk0xlqshape_marks_pos (T : GGKacType)
    (i : Fin (k0DiagOf T).marks.length) :
    0 < (k0DiagOf T).marks.getD i.val 0 := by
  cases T <;> fin_cases i <;> decide

private def lk0xlqshape_iOf (n : ℕ) (c : List ℕ) : ℕ :=
  ((List.range n).filter (fun i => decide (i ∉ c))).headD 0

private def lk0xlqshape_vcoord {τ : Tag} (v : Fin τ.rank → ℤ) (x : ℕ) : ℤ :=
  if h : x < τ.rank then v ⟨x, h⟩ else 0

private def lk0xlqshape_inSpan (τ : Tag) (D : K0Diag) (c : List ℕ)
    (v : Fin τ.rank → ℤ) : Bool :=
  if _ : 0 ∈ c then
    decide (((D.marks.getD (lk0xlqshape_iOf D.marks.length c) 0 : ℕ) : ℤ) ∣
        lk0xlqshape_vcoord v (lk0xlqshape_iOf D.marks.length c - 1)) &&
      decide (∀ j : Fin τ.rank, j.val + 1 ∉ c →
        v j * ((D.marks.getD (lk0xlqshape_iOf D.marks.length c) 0 : ℕ) : ℤ) =
          lk0xlqshape_vcoord v (lk0xlqshape_iOf D.marks.length c - 1) *
            ((D.marks.getD (j.val + 1) 0 : ℕ) : ℤ))
  else
    decide (∀ j : Fin τ.rank, j.val + 1 ∉ c → v j = 0)

private def lk0xlqshape_coeff (τ : Tag) (D : K0Diag) (c : List ℕ)
    (v : Fin τ.rank → ℤ) (x : ℕ) : ℤ :=
  if _ : 0 ∈ c then
    let n0 : ℤ := - lk0xlqshape_vcoord v (lk0xlqshape_iOf D.marks.length c - 1) /
      ((D.marks.getD (lk0xlqshape_iOf D.marks.length c) 0 : ℕ) : ℤ)
    if x = 0 then n0
    else if x ∈ c then
      lk0xlqshape_vcoord v (x - 1) + n0 * ((D.marks.getD x 0 : ℕ) : ℤ)
    else 0
  else
    if x ∈ c then lk0xlqshape_vcoord v (x - 1) else 0

private def lk0xlqshape_signCoh (τ : Tag) (D : K0Diag) (c : List ℕ)
    (v : Fin τ.rank → ℤ) : Bool :=
  decide ((∀ x ∈ c, 0 ≤ lk0xlqshape_coeff τ D c v x) ∨
    ∀ x ∈ c, lk0xlqshape_coeff τ D c v x ≤ 0)

private def lk0xlqshape_rootList (τ : Tag) : List (Fin τ.rank → ℤ) :=
  (List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root

private def lk0xlqshape_comps : GGKacType → List (List ℕ)
  | .E6 => [[0], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5], [0, 2], [0, 2, 3, 4], [0, 2, 3, 4, 5],
      [0, 2, 3, 4, 5, 6], [0, 2, 4], [0, 2, 4, 5], [0, 2, 4, 5, 6], [1], [1, 2, 3, 4],
      [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 3], [1, 3, 4], [1, 3, 4, 5], [1, 3, 4, 5, 6],
      [2], [2, 3, 4], [2, 3, 4, 5], [2, 3, 4, 5, 6], [2, 4], [2, 4, 5], [2, 4, 5, 6], [3],
      [3, 4], [3, 4, 5], [3, 4, 5, 6], [4], [4, 5], [4, 5, 6], [5], [5, 6], [6]]
  | .E7 => [[0], [0, 1], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6], [0, 1, 3],
      [0, 1, 3, 4], [0, 1, 3, 4, 5], [0, 1, 3, 4, 5, 6], [0, 1, 3, 4, 5, 6, 7], [1], [1, 2, 3, 4],
      [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7], [1, 3], [1, 3, 4], [1, 3, 4, 5],
      [1, 3, 4, 5, 6], [1, 3, 4, 5, 6, 7], [2], [2, 3, 4], [2, 3, 4, 5], [2, 3, 4, 5, 6],
      [2, 3, 4, 5, 6, 7], [2, 4], [2, 4, 5], [2, 4, 5, 6], [2, 4, 5, 6, 7], [3], [3, 4], [3, 4, 5],
      [3, 4, 5, 6], [3, 4, 5, 6, 7], [4], [4, 5], [4, 5, 6], [4, 5, 6, 7], [5], [5, 6], [5, 6, 7],
      [6], [6, 7], [7]]
  | .E8 => [[0], [0, 1, 3, 4, 5, 6, 7, 8], [0, 2, 3, 4, 5, 6, 7, 8], [0, 2, 4, 5, 6, 7, 8],
      [0, 3, 4, 5, 6, 7, 8], [0, 4, 5, 6, 7, 8], [0, 5, 6, 7, 8], [0, 6, 7, 8], [0, 7, 8], [0, 8],
      [1], [1, 2, 3, 4], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 7],
      [1, 2, 3, 4, 5, 6, 7, 8], [1, 3], [1, 3, 4], [1, 3, 4, 5], [1, 3, 4, 5, 6],
      [1, 3, 4, 5, 6, 7], [1, 3, 4, 5, 6, 7, 8], [2], [2, 3, 4], [2, 3, 4, 5], [2, 3, 4, 5, 6],
      [2, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 7, 8], [2, 4], [2, 4, 5], [2, 4, 5, 6], [2, 4, 5, 6, 7],
      [2, 4, 5, 6, 7, 8], [3], [3, 4], [3, 4, 5], [3, 4, 5, 6], [3, 4, 5, 6, 7],
      [3, 4, 5, 6, 7, 8], [4], [4, 5], [4, 5, 6], [4, 5, 6, 7], [4, 5, 6, 7, 8], [5], [5, 6],
      [5, 6, 7], [5, 6, 7, 8], [6], [6, 7], [6, 7, 8], [7], [7, 8], [8]]
  | .F4 => [[0], [0, 1], [0, 1, 2], [0, 1, 2, 3], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [2], [2, 3],
      [2, 3, 4], [3], [3, 4], [4]]

private def lk0xlqshape_checkComp (τ : Tag) (roots : List (Fin τ.rank → ℤ)) (D : K0Diag)
    (c : List ℕ) : Bool :=
  roots.all (fun v => (!lk0xlqshape_inSpan τ D c v) || lk0xlqshape_signCoh τ D c v) &&
    ((roots.filter (fun v => lk0xlqshape_inSpan τ D c v)).length ==
      lqShapeCount (k0CompType D c))

private theorem lk0xlqshape_mem_rootList {τ : Tag}
    {v : Fin τ.rank → ℤ} :
    v ∈ lk0xlqshape_rootList τ ↔ IsRoot τ v := by
  rw [lk0xlqshape_rootList, ← mem_rootFinset, rootFinset, List.mem_toFinset]

private theorem lk0xlqshape_rootList_nodup (τ : Tag) :
    (lk0xlqshape_rootList τ).Nodup := by
  have h := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
  have heq : (List.map (fun k => List.ofFn (τ.rootCertificate.root k))
      (List.range τ.rootCertificate.roots.length)) =
      (List.map (fun v : Fin τ.rank → ℤ => List.ofFn v) (lk0xlqshape_rootList τ)) := by
    rw [lk0xlqshape_rootList, List.map_map]
    rfl
  rw [heq] at h
  exact List.Nodup.of_map (fun v : Fin τ.rank → ℤ => List.ofFn v) h

private theorem lk0xlqshape_lqExtRoot_apply (T : GGKacType) (x : ℕ)
    (j : Fin (absTag T).rank) :
    lqExtRoot (absTag T) T x j =
      (if x = 0 then -(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)
        else if j.val + 1 = x then 1 else 0) := rfl

private theorem lk0xlqshape_vcoord_eq (T : GGKacType) (v : Fin (absTag T).rank → ℤ)
    {y : ℕ} (hy : y < (absTag T).rank) :
    lk0xlqshape_vcoord v y = v ⟨y, hy⟩ := by
  unfold lk0xlqshape_vcoord
  rw [dif_pos hy]

private theorem lk0xlqshape_vcoord_fin (T : GGKacType) (v : Fin (absTag T).rank → ℤ)
    (j : Fin (absTag T).rank) :
    lk0xlqshape_vcoord v j.val = v j := by
  unfold lk0xlqshape_vcoord
  rw [dif_pos j.isLt]

private theorem lk0xlqshape_vcoord_ext (T : GGKacType) (x : ℕ) {y : ℕ}
    (hy : y < (absTag T).rank) :
    lk0xlqshape_vcoord (lqExtRoot (absTag T) T x) y =
      (if x = 0 then -(((k0DiagOf T).marks.getD (y + 1) 0 : ℕ) : ℤ)
        else if y + 1 = x then 1 else 0) := by
  rw [lk0xlqshape_vcoord_eq T _ hy]
  exact lk0xlqshape_lqExtRoot_apply T x ⟨y, hy⟩

private theorem lk0xlqshape_vcoord_add (T : GGKacType) (v u : Fin (absTag T).rank → ℤ)
    (x : ℕ) :
    lk0xlqshape_vcoord (v + u) x = lk0xlqshape_vcoord v x + lk0xlqshape_vcoord u x := by
  unfold lk0xlqshape_vcoord
  by_cases h : x < (absTag T).rank
  · rw [dif_pos h, dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, dif_neg h]; ring

private theorem lk0xlqshape_vcoord_smul (T : GGKacType) (a : ℤ)
    (v : Fin (absTag T).rank → ℤ) (x : ℕ) :
    lk0xlqshape_vcoord (a • v) x = a * lk0xlqshape_vcoord v x := by
  unfold lk0xlqshape_vcoord
  by_cases h : x < (absTag T).rank
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; ring

private theorem lk0xlqshape_vcoord_zero (T : GGKacType) (x : ℕ) :
    lk0xlqshape_vcoord (0 : Fin (absTag T).rank → ℤ) x = 0 := by
  unfold lk0xlqshape_vcoord
  split <;> rfl

private theorem lk0xlqshape_headD_mem {α : Type*} (l : List α) (d : α) (h : l ≠ []) :
    l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [List.headD_cons]

private theorem lk0xlqshape_iOf_mem (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c) :
    lk0xlqshape_iOf (k0DiagOf T).marks.length c ∈
      (List.range (k0DiagOf T).marks.length).filter (fun i => decide (i ∉ c)) := by
  obtain ⟨i, hi, hic⟩ := hproper
  have hmem : i ∈ (List.range (k0DiagOf T).marks.length).filter
      (fun i => decide (i ∉ c)) := by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hi, hic⟩
  have hne : (List.range (k0DiagOf T).marks.length).filter
      (fun i => decide (i ∉ c)) ≠ [] := by
    intro h
    rw [h] at hmem
    simp at hmem
  unfold lk0xlqshape_iOf
  exact lk0xlqshape_headD_mem _ _ hne

private theorem lk0xlqshape_iOf_lt (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c) :
    lk0xlqshape_iOf (k0DiagOf T).marks.length c < (k0DiagOf T).marks.length := by
  have h := lk0xlqshape_iOf_mem T hproper
  rw [List.mem_filter] at h
  exact List.mem_range.mp h.1

private theorem lk0xlqshape_iOf_notMem (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c) :
    lk0xlqshape_iOf (k0DiagOf T).marks.length c ∉ c := by
  have h := lk0xlqshape_iOf_mem T hproper
  rw [List.mem_filter] at h
  have := h.2
  simpa using this

private theorem lk0xlqshape_iOf_pos (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c) (h0 : 0 ∈ c) :
    1 ≤ lk0xlqshape_iOf (k0DiagOf T).marks.length c := by
  have hnot := lk0xlqshape_iOf_notMem T hproper
  rcases Nat.eq_zero_or_pos (lk0xlqshape_iOf (k0DiagOf T).marks.length c) with h | h
  · exfalso; apply hnot; rw [h]; exact h0
  · exact h

private theorem lk0xlqshape_inSpan_eq_true (T : GGKacType) {c : List ℕ} (hc0 : 0 ∈ c)
    (v : Fin (absTag T).rank → ℤ) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true ↔
      (((k0DiagOf T).marks.getD (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ) ∣
          lk0xlqshape_vcoord v (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) ∧
        ∀ j : Fin (absTag T).rank, j.val + 1 ∉ c →
          v j * (((k0DiagOf T).marks.getD
              (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ) =
            lk0xlqshape_vcoord v (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) *
              (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) := by
  unfold lk0xlqshape_inSpan
  rw [dif_pos hc0, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

private theorem lk0xlqshape_inSpan_eq_true' (T : GGKacType) {c : List ℕ} (hc0 : 0 ∉ c)
    (v : Fin (absTag T).rank → ℤ) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true ↔
      ∀ j : Fin (absTag T).rank, j.val + 1 ∉ c → v j = 0 := by
  unfold lk0xlqshape_inSpan
  rw [dif_neg hc0, decide_eq_true_eq]

private theorem lk0xlqshape_sum_apply (T : GGKacType) (c : List ℕ) (f : ℕ → ℤ)
    (j : Fin (absTag T).rank) :
    (∑ x ∈ c.toFinset, f x * lqExtRoot (absTag T) T x j) =
      (if 0 ∈ c then
          f 0 * (-(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)) else 0) +
        (if j.val + 1 ∈ c then f (j.val + 1) else 0) := by
  set A : ℤ := f 0 * (-(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)) with hA
  have ha0 : j.val + 1 ≠ 0 := by omega
  have key : ∀ x ∈ c.toFinset,
      f x * lqExtRoot (absTag T) T x j =
        (if x = 0 then A else 0) + (if x = j.val + 1 then f x else 0) := by
    intro x hx
    rw [lk0xlqshape_lqExtRoot_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [if_pos rfl, if_neg (Ne.symm ha0), add_zero]
      exact hA.symm
    · rw [if_neg hx0]
      by_cases hxa : j.val + 1 = x
      · subst hxa
        simp [ha0]
      · rw [if_neg hxa]
        rw [if_neg hx0, if_neg (fun h : x = j.val + 1 => hxa h.symm)]
        ring
  calc
    (∑ x ∈ c.toFinset, f x * lqExtRoot (absTag T) T x j)
        = ∑ x ∈ c.toFinset,
            ((if x = 0 then A else 0) + (if x = j.val + 1 then f x else 0)) :=
          Finset.sum_congr rfl key
    _ = (∑ x ∈ c.toFinset, (if x = 0 then A else 0)) +
          (∑ x ∈ c.toFinset, (if x = j.val + 1 then f x else 0)) := Finset.sum_add_distrib
    _ = (if 0 ∈ c.toFinset then A else 0) +
          (if j.val + 1 ∈ c.toFinset then f (j.val + 1) else 0) := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    _ = (if 0 ∈ c then A else 0) + (if j.val + 1 ∈ c then f (j.val + 1) else 0) := by
          simp only [List.mem_toFinset]
    _ = (if 0 ∈ c then
          f 0 * (-(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)) else 0) +
        (if j.val + 1 ∈ c then f (j.val + 1) else 0) := by rw [hA]

private theorem lk0xlqshape_coeff_zero (T : GGKacType) {c : List ℕ} (hc0 : 0 ∈ c)
    (v : Fin (absTag T).rank → ℤ) :
    lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 =
      - lk0xlqshape_vcoord v (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) /
        (((k0DiagOf T).marks.getD (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ) := by
  unfold lk0xlqshape_coeff
  rw [dif_pos hc0, if_pos rfl]

private theorem lk0xlqshape_coeff_mem (T : GGKacType) {c : List ℕ} (hc0 : 0 ∈ c)
    (v : Fin (absTag T).rank → ℤ) {x : ℕ} (hx : x ∈ c) (hx0 : x ≠ 0) :
    lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x =
      lk0xlqshape_vcoord v (x - 1) +
        lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
          (((k0DiagOf T).marks.getD x 0 : ℕ) : ℤ) := by
  rw [lk0xlqshape_coeff_zero T hc0 v]
  unfold lk0xlqshape_coeff
  rw [dif_pos hc0, if_neg hx0, if_pos hx]

private theorem lk0xlqshape_coeff_notMem (T : GGKacType) {c : List ℕ}
    (v : Fin (absTag T).rank → ℤ) {x : ℕ} (hx : x ∉ c) :
    lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x = 0 := by
  unfold lk0xlqshape_coeff
  by_cases hc0 : 0 ∈ c
  · rw [dif_pos hc0]
    by_cases hx0 : x = 0
    · exact absurd (hx0 ▸ hc0) hx
    · rw [if_neg hx0, if_neg (fun h : x ∈ c => hx h)]
  · rw [dif_neg hc0, if_neg (fun h : x ∈ c => hx h)]

private theorem lk0xlqshape_zero_inSpan (T : GGKacType) (c : List ℕ) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c 0 = true := by
  by_cases hc0 : 0 ∈ c
  · rw [lk0xlqshape_inSpan_eq_true T hc0]
    refine ⟨?_, ?_⟩
    · rw [lk0xlqshape_vcoord_zero]; exact dvd_zero _
    · intro j hj; rw [lk0xlqshape_vcoord_zero]; simp
  · rw [lk0xlqshape_inSpan_eq_true' T hc0]
    intro j hj; rfl

private theorem lk0xlqshape_add_inSpan (T : GGKacType) {c : List ℕ}
    {v u : Fin (absTag T).rank → ℤ}
    (hv : lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true)
    (hu : lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c u = true) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c (v + u) = true := by
  by_cases hc0 : 0 ∈ c
  · rw [lk0xlqshape_inSpan_eq_true T hc0] at hv hu ⊢
    obtain ⟨hdv, hev⟩ := hv
    obtain ⟨hdu, heu⟩ := hu
    refine ⟨?_, ?_⟩
    · rw [lk0xlqshape_vcoord_add]; exact dvd_add hdv hdu
    · intro j hj
      rw [lk0xlqshape_vcoord_add]
      simp only [Pi.add_apply]
      have hvj := hev j hj
      have huj := heu j hj
      linear_combination hvj + huj
  · rw [lk0xlqshape_inSpan_eq_true' T hc0] at hv hu ⊢
    intro j hj
    simp only [Pi.add_apply, hv j hj, hu j hj, add_zero]

private theorem lk0xlqshape_smul_inSpan (T : GGKacType) {c : List ℕ} (a : ℤ)
    {v : Fin (absTag T).rank → ℤ}
    (hv : lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c (a • v) = true := by
  by_cases hc0 : 0 ∈ c
  · rw [lk0xlqshape_inSpan_eq_true T hc0] at hv ⊢
    obtain ⟨hdv, hev⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [lk0xlqshape_vcoord_smul]; exact dvd_mul_of_dvd_right hdv a
    · intro j hj
      rw [lk0xlqshape_vcoord_smul]
      simp only [Pi.smul_apply]
      have hvj := hev j hj
      linear_combination a * hvj
  · rw [lk0xlqshape_inSpan_eq_true' T hc0] at hv ⊢
    intro j hj
    simp only [Pi.smul_apply, hv j hj, smul_eq_mul, mul_zero]

private theorem lk0xlqshape_gen_inSpan (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c) {x : ℕ} (hx : x ∈ c) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c (lqExtRoot (absTag T) T x) = true := by
  have hi_not := lk0xlqshape_iOf_notMem T hproper
  have hi_lt := lk0xlqshape_iOf_lt T hproper
  by_cases hc0 : 0 ∈ c
  · have hi_pos := lk0xlqshape_iOf_pos T hproper hc0
    have hi_rank : lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1 < (absTag T).rank := by
      have := lk0xlqshape_marks_length T; omega
    rw [lk0xlqshape_inSpan_eq_true T hc0]
    refine ⟨?_, ?_⟩
    · rw [lk0xlqshape_vcoord_ext T x hi_rank]
      by_cases hx0 : x = 0
      · subst hx0
        rw [if_pos rfl]
        have hii : lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1 + 1 =
            lk0xlqshape_iOf (k0DiagOf T).marks.length c := Nat.sub_add_cancel hi_pos
        rw [hii]
        exact dvd_neg.mpr (dvd_refl _)
      · rw [if_neg hx0]
        have hne : lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1 + 1 ≠ x := by
          intro h
          rw [Nat.sub_add_cancel hi_pos] at h
          exact hi_not (h.symm ▸ hx)
        rw [if_neg hne]
        exact dvd_zero _
    · intro j hj
      rw [lk0xlqshape_vcoord_ext T x hi_rank]
      by_cases hx0 : x = 0
      · subst hx0
        rw [if_pos rfl, lk0xlqshape_lqExtRoot_apply, if_pos rfl]
        have hii : lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1 + 1 =
            lk0xlqshape_iOf (k0DiagOf T).marks.length c := Nat.sub_add_cancel hi_pos
        rw [hii]; ring
      · rw [if_neg hx0, lk0xlqshape_lqExtRoot_apply, if_neg hx0]
        have hnej : j.val + 1 ≠ x := by intro h; exact hj (h.symm ▸ hx)
        have hix : (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) + 1 ≠ x := by
          intro h
          rw [Nat.sub_add_cancel hi_pos] at h
          exact hi_not (h.symm ▸ hx)
        rw [if_neg hnej, if_neg hix]
        ring
  · rw [lk0xlqshape_inSpan_eq_true' T hc0]
    intro j hj
    rw [lk0xlqshape_lqExtRoot_apply]
    have hx0 : x ≠ 0 := fun h => hc0 (h ▸ hx)
    rw [if_neg hx0]
    have hne : j.val + 1 ≠ x := by intro h; exact hj (h.symm ▸ hx)
    exact if_neg hne

private theorem lk0xlqshape_span_le_inSpan (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c)
    (v : Fin (absTag T).rank → ℤ)
    (hv : v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot (absTag T) T x}) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true := by
  let P : Submodule ℤ (Fin (absTag T).rank → ℤ) :=
    { carrier := {w | lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c w = true}
      zero_mem' := lk0xlqshape_zero_inSpan T c
      add_mem' := fun hv hu => lk0xlqshape_add_inSpan T hv hu
      smul_mem' := fun a _x hv => lk0xlqshape_smul_inSpan T a hv }
  exact (Submodule.span_le.mpr (fun w hw => by
    rcases hw with ⟨x, hx, rfl⟩
    exact lk0xlqshape_gen_inSpan T hproper hx) : _ ≤ P) hv

private theorem lk0xlqshape_inSpan_spec (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c)
    (v : Fin (absTag T).rank → ℤ)
    (hin : lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true) :
    v = ∑ x ∈ c.toFinset,
      lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x • lqExtRoot (absTag T) T x := by
  ext j
  have hsum : (∑ x ∈ c.toFinset,
        lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x • lqExtRoot (absTag T) T x) j
      = ∑ x ∈ c.toFinset,
        lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x * lqExtRoot (absTag T) T x j := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, lk0xlqshape_sum_apply]
  by_cases hc0 : 0 ∈ c
  · have hin' := (lk0xlqshape_inSpan_eq_true T hc0 v).mp hin
    obtain ⟨hdiv, heq⟩ := hin'
    have hmi_ne : (((k0DiagOf T).marks.getD
        (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ) ≠ 0 := by
      have hp := lk0xlqshape_marks_pos T ⟨lk0xlqshape_iOf (k0DiagOf T).marks.length c,
        lk0xlqshape_iOf_lt T hproper⟩
      exact_mod_cast ne_of_gt hp
    have hn0 : lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
        (((k0DiagOf T).marks.getD
            (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ)
        = - lk0xlqshape_vcoord v (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) := by
      rw [lk0xlqshape_coeff_zero T hc0 v]
      exact Int.ediv_mul_cancel (dvd_neg.mpr hdiv)
    rw [if_pos hc0]
    by_cases hj : j.val + 1 ∈ c
    · rw [if_pos hj]
      have hcoeff : lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v (j.val + 1) =
          v j + lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
            (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) := by
        rw [lk0xlqshape_coeff_mem T hc0 v hj (by omega : j.val + 1 ≠ 0),
          Nat.add_sub_cancel, lk0xlqshape_vcoord_fin]
      rw [hcoeff]; ring
    · rw [if_neg hj]
      have hgoal : lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
          (-(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)) = v j := by
        apply mul_right_cancel₀ hmi_ne
        calc lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
              (-(((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ)) *
                (((k0DiagOf T).marks.getD
                    (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ)
            = - (lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v 0 *
                (((k0DiagOf T).marks.getD
                    (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ)) *
                (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) := by ring
          _ = - (- lk0xlqshape_vcoord v
                (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1)) *
                (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) := by rw [hn0]
          _ = lk0xlqshape_vcoord v
                (lk0xlqshape_iOf (k0DiagOf T).marks.length c - 1) *
                (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) := by ring
          _ = v j * (((k0DiagOf T).marks.getD
                (lk0xlqshape_iOf (k0DiagOf T).marks.length c) 0 : ℕ) : ℤ) := (heq j hj).symm
      rw [hgoal, add_zero]
  · have hin' := (lk0xlqshape_inSpan_eq_true' T hc0 v).mp hin
    rw [if_neg hc0]
    by_cases hj : j.val + 1 ∈ c
    · rw [if_pos hj]
      have hcoeff : lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v (j.val + 1) = v j := by
        unfold lk0xlqshape_coeff
        rw [dif_neg hc0, if_pos hj, Nat.add_sub_cancel, lk0xlqshape_vcoord_fin]
      rw [hcoeff, zero_add]
    · rw [if_neg hj]
      simp [hin' j hj]

private theorem lk0xlqshape_inSpan_iff_span (T : GGKacType) {c : List ℕ}
    (hproper : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c)
    (v : Fin (absTag T).rank → ℤ) :
    lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true ↔
      v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot (absTag T) T x} := by
  constructor
  · intro hin
    have hspec := lk0xlqshape_inSpan_spec T hproper v hin
    have hgen : ∀ t : Finset ℕ, (∀ x ∈ t, x ∈ c) →
        Finset.sum t (fun x : ℕ =>
          (lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x : ℤ) •
            (lqExtRoot (absTag T) T x : Fin (absTag T).rank → ℤ)) ∈
          Submodule.span ℤ {w : Fin (absTag T).rank → ℤ |
            ∃ x ∈ c, w = lqExtRoot (absTag T) T x} := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; simp
      | insert a s has ih =>
          intro hsub
          rw [Finset.sum_insert has]
          refine Submodule.add_mem _
            (Submodule.smul_mem _ (lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v a)
              (Submodule.subset_span
                ⟨a, hsub a (Finset.mem_insert_self a s), rfl⟩)) (ih ?_)
          intro x hx
          exact hsub x (Finset.mem_insert_of_mem hx)
    rw [hspec]
    exact hgen c.toFinset (fun x hx => List.mem_toFinset.mp hx)
  · intro hv
    exact lk0xlqshape_span_le_inSpan T hproper v hv

private theorem lk0xlqshape_sign_combination (T : GGKacType) {c : List ℕ}
    (v : Fin (absTag T).rank → ℤ)
    (hcoeff : v = ∑ x ∈ c.toFinset,
      lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x • lqExtRoot (absTag T) T x)
    (hsign : (∀ x ∈ c, 0 ≤ lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x) ∨
      ∀ x ∈ c, lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x ≤ 0) :
    ∃ n : ℕ → ℕ, (∀ x, n x ≠ 0 → x ∈ c) ∧
      (v = ∑ x ∈ c.toFinset, (n x : ℤ) • lqExtRoot (absTag T) T x ∨
        v = -∑ x ∈ c.toFinset, (n x : ℤ) • lqExtRoot (absTag T) T x) := by
  rcases hsign with hnonneg | hnonpos
  · refine ⟨fun x => (lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x).toNat, ?_, Or.inl ?_⟩
    · intro x hx
      by_contra hxc
      have hz := lk0xlqshape_coeff_notMem T v hxc
      simp [hz] at hx
    · calc v = ∑ x ∈ c.toFinset,
            lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x • lqExtRoot (absTag T) T x := hcoeff
        _ = ∑ x ∈ c.toFinset,
            ((lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x).toNat : ℤ) •
              lqExtRoot (absTag T) T x := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [Int.toNat_of_nonneg (hnonneg x (by simpa using hx))]
  · refine ⟨fun x => (- lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x).toNat, ?_, Or.inr ?_⟩
    · intro x hx
      by_contra hxc
      have hz := lk0xlqshape_coeff_notMem T v hxc
      simp [hz] at hx
    · calc v = ∑ x ∈ c.toFinset,
            lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x • lqExtRoot (absTag T) T x := hcoeff
        _ = - ∑ x ∈ c.toFinset,
            ((- lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x).toNat : ℤ) •
              lqExtRoot (absTag T) T x := by
              rw [← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl (fun x hx => ?_)
              have hx' : ((- lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x).toNat : ℤ) =
                  - lk0xlqshape_coeff (absTag T) (k0DiagOf T) c v x :=
                Int.toNat_of_nonneg (by linarith [hnonpos x (by simpa using hx)])
              rw [hx']
              simp

private theorem lk0xlqshape_check (T : GGKacType) :
    (∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      zero.length < (k0DiagOf T).marks.length →
      ∀ c ∈ k0Comps (k0DiagOf T) zero, c ∈ lk0xlqshape_comps T) ∧
    (lk0xlqshape_comps T).all
      (lk0xlqshape_checkComp (absTag T) (lk0xlqshape_rootList (absTag T)) (k0DiagOf T))
      = true := by
  cases T <;> decide +kernel

theorem lq_cone_table (τ : Tag) (T : GGKacType)
    (hτ : absTag T = τ) {zero : List ℕ}
    (hz : zero.Sublist (List.range (k0DiagOf T).marks.length))
    (hproper : zero.length < (k0DiagOf T).marks.length) {c : List ℕ}
    (hc : c ∈ k0Comps (k0DiagOf T) zero) (v : Fin τ.rank → ℤ) (hv : IsRoot τ v)
    (hspan : v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot τ T x}) :
    ∃ n : ℕ → ℕ, (∀ x, n x ≠ 0 → x ∈ c) ∧
      (v = ∑ x ∈ c.toFinset, (n x : ℤ) • lqExtRoot τ T x ∨
        v = -∑ x ∈ c.toFinset, (n x : ℤ) • lqExtRoot τ T x) := by
  subst τ
  have hnd_zero : zero.Nodup := hz.nodup List.nodup_range
  obtain ⟨-, hc_pair, hc_sub⟩ := (k0Comps_spec (k0DiagOf T) hnd_zero).1 c hc
  have hc_nd : c.Nodup := List.nodup_iff_pairwise_ne.mpr (hc_pair.imp (fun h => ne_of_lt h))
  have hproper' : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c := by
    by_contra h
    push Not at h
    have hsub_range : List.range (k0DiagOf T).marks.length ⊆ c :=
      fun i hi => h i (List.mem_range.mp hi)
    have hcard : (List.range (k0DiagOf T).marks.length).toFinset ⊆ c.toFinset := by
      intro i hi; simp only [List.mem_toFinset] at hi ⊢; exact hsub_range hi
    have hcard' := Finset.card_le_card hcard
    rw [List.toFinset_card_of_nodup List.nodup_range, List.toFinset_card_of_nodup hc_nd] at hcard'
    have hclt : c.length < (k0DiagOf T).marks.length := by
      have hcz : c.toFinset ⊆ zero.toFinset := by
        intro i hi; simp only [List.mem_toFinset] at hi ⊢; exact hc_sub i hi
      have hc2 := Finset.card_le_card hcz
      rw [List.toFinset_card_of_nodup hc_nd, List.toFinset_card_of_nodup hnd_zero] at hc2
      omega
    have hlen : (List.range (k0DiagOf T).marks.length).length ≤ c.length := by
      simpa using hcard'
    rw [List.length_range] at hlen
    omega
  have hspan_in : lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true :=
    (lk0xlqshape_inSpan_iff_span T hproper' v).mpr hspan
  have hv_mem : v ∈ lk0xlqshape_rootList (absTag T) := lk0xlqshape_mem_rootList.mpr hv
  have hmem_comps : c ∈ lk0xlqshape_comps T :=
    (lk0xlqshape_check T).1 zero (List.mem_sublists.mpr hz) hproper c hc
  have hcomp := List.all_eq_true.mp (lk0xlqshape_check T).2 c hmem_comps
  rw [lk0xlqshape_checkComp, Bool.and_eq_true] at hcomp
  obtain ⟨hall, -⟩ := hcomp
  have hroot := List.all_eq_true.mp hall v hv_mem
  rw [Bool.or_eq_true] at hroot
  have hsignCoh : lk0xlqshape_signCoh (absTag T) (k0DiagOf T) c v = true := by
    rcases hroot with h | h
    · rw [hspan_in] at h; simp at h
    · exact h
  have hsign := of_decide_eq_true hsignCoh
  exact lk0xlqshape_sign_combination T v
    (lk0xlqshape_inSpan_spec T hproper' v hspan_in) hsign

theorem lq_shape_table (τ : Tag) (T : GGKacType)
    (hτ : absTag T = τ) {zero : List ℕ}
    (hz : zero.Sublist (List.range (k0DiagOf T).marks.length))
    (hproper : zero.length < (k0DiagOf T).marks.length) {c : List ℕ}
    (hc : c ∈ k0Comps (k0DiagOf T) zero) :
    {v : Fin τ.rank → ℤ | IsRoot τ v ∧
        v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot τ T x}}.ncard =
      lqShapeCount (k0CompType (k0DiagOf T) c) := by
  subst τ
  have hnd_zero : zero.Nodup := hz.nodup List.nodup_range
  obtain ⟨-, hc_pair, hc_sub⟩ := (k0Comps_spec (k0DiagOf T) hnd_zero).1 c hc
  have hc_nd : c.Nodup := List.nodup_iff_pairwise_ne.mpr (hc_pair.imp (fun h => ne_of_lt h))
  have hproper' : ∃ i, i < (k0DiagOf T).marks.length ∧ i ∉ c := by
    by_contra h
    push Not at h
    have hsub_range : List.range (k0DiagOf T).marks.length ⊆ c :=
      fun i hi => h i (List.mem_range.mp hi)
    have hcard : (List.range (k0DiagOf T).marks.length).toFinset ⊆ c.toFinset := by
      intro i hi; simp only [List.mem_toFinset] at hi ⊢; exact hsub_range hi
    have hcard' := Finset.card_le_card hcard
    rw [List.toFinset_card_of_nodup List.nodup_range, List.toFinset_card_of_nodup hc_nd] at hcard'
    have hclt : c.length < (k0DiagOf T).marks.length := by
      have hcz : c.toFinset ⊆ zero.toFinset := by
        intro i hi; simp only [List.mem_toFinset] at hi ⊢; exact hc_sub i hi
      have hc2 := Finset.card_le_card hcz
      rw [List.toFinset_card_of_nodup hc_nd, List.toFinset_card_of_nodup hnd_zero] at hc2
      omega
    have hlen : (List.range (k0DiagOf T).marks.length).length ≤ c.length := by
      simpa using hcard'
    rw [List.length_range] at hlen
    omega
  have hset : {v : Fin (absTag T).rank → ℤ | IsRoot (absTag T) v ∧
        v ∈ Submodule.span ℤ {w | ∃ x ∈ c, w = lqExtRoot (absTag T) T x}} =
      ↑((rootFinset (absTag T)).filter (fun v =>
          lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true)) := by
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_coe, mem_rootFinset]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (lk0xlqshape_inSpan_iff_span T hproper' v).mpr h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (lk0xlqshape_inSpan_iff_span T hproper' v).mp h2⟩⟩
  rw [hset, Set.ncard_coe_finset]
  have hcard_eq : ((rootFinset (absTag T)).filter (fun v =>
        lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true)).card =
      ((lk0xlqshape_rootList (absTag T)).filter
        (fun v => lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v)).length := by
    rw [show ((rootFinset (absTag T)).filter (fun v =>
          lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v = true)) =
        ((lk0xlqshape_rootList (absTag T)).filter
          (fun v => lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v)).toFinset from by
      ext v
      simp only [Finset.mem_filter, mem_rootFinset, List.mem_toFinset, List.mem_filter,
        lk0xlqshape_mem_rootList]]
    rw [List.toFinset_card_of_nodup]
    exact (lk0xlqshape_rootList_nodup (absTag T)).filter _
  have hmem_comps : c ∈ lk0xlqshape_comps T :=
    (lk0xlqshape_check T).1 zero (List.mem_sublists.mpr hz) hproper c hc
  have hcomp := List.all_eq_true.mp (lk0xlqshape_check T).2 c hmem_comps
  rw [lk0xlqshape_checkComp, Bool.and_eq_true] at hcomp
  obtain ⟨-, hcount⟩ := hcomp
  have hcount' : ((lk0xlqshape_rootList (absTag T)).filter
        (fun v => lk0xlqshape_inSpan (absTag T) (k0DiagOf T) c v)).length =
      lqShapeCount (k0CompType (k0DiagOf T) c) := by
    have := beq_iff_eq.mp hcount
    exact this
  rw [hcard_eq, hcount']

end CFSG.StandardType.GGK0LQ

end
