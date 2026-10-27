module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace R4J

theorem monoid_schreier {M Y : Type*} [Monoid M] [MulAction M Y] (S : Set M) (W : Submonoid M)
    (y : Y) (O : Set Y) (t : Y → M) (hty : t y = 1) (hyO : y ∈ O)
    (hS : ∀ o ∈ O, ∀ s ∈ S, s • o ∈ O ∧ ∃ w ∈ W, s * t o = t (s • o) * w) :
    ∀ g ∈ Submonoid.closure S, g • y = y → g ∈ W := by
  intro g hg hgy
  have key : ∀ g ∈ Submonoid.closure S, g • y ∈ O ∧ ∃ w ∈ W, g = t (g • y) * w := by
    intro g hg
    induction hg using Submonoid.closure_induction_left with
    | one => exact ⟨by simpa using hyO, 1, W.one_mem, by simp [hty]⟩
    | mul_left s hs g hg ih =>
      obtain ⟨hgO, w, hw, hgw⟩ := ih
      obtain ⟨hsO, w', hw', hsw⟩ := hS (g • y) hgO s hs
      refine ⟨by rwa [mul_smul], w' * w, W.mul_mem hw' hw, ?_⟩
      rw [mul_smul]
      calc s * g = s * (t (g • y) * w) := congrArg (s * ·) hgw
        _ = (s * t (g • y)) * w := by rw [mul_assoc]
        _ = (t (s • g • y) * w') * w := by rw [hsw]
        _ = t (s • g • y) * (w' * w) := by rw [mul_assoc]
  obtain ⟨-, w, hw, hgw⟩ := key g hg
  rw [hgy, hty, one_mul] at hgw
  rw [hgw]
  exact hw

abbrev N5 : Type := Option (Fin 4)

@[expose] def reflM (X : Matrix N5 N5 ℤ) (o : N5) : Matrix N5 N5 (ZMod 3) :=
  Matrix.of fun i j => (if i = j then 1 else 0) - (if i = o then ((X o j : ℤ) : ZMod 3) else 0)

@[expose] def caseC (ori : Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  if ori then CartanMatrix.F₄ else Matrix.transpose CartanMatrix.F₄

@[expose] def caseB (cell : Bool) : Fin 4 := if cell then 0 else 3

@[expose] def caseCN (cell : Bool) : Fin 4 := if cell then 1 else 2

@[expose] def caseX (ori cell : Bool) : Matrix N5 N5 ℤ := ggAttachCartan (caseC ori) (caseCN cell)

@[reducible] private def r4d_idx (o : N5) : Fin 5 :=
  match o with
  | some i => ⟨i.val, by omega⟩
  | none => 4

@[reducible] private def r4d_dec (n : ℕ) : N5 → ZMod 3 :=
  fun o => (((n / 3 ^ (r4d_idx o).val) % 3 : ℕ) : ZMod 3)

@[reducible] private def r4d_key (v : N5 → ZMod 3) : List ℕ :=
  [(v none).val, (v (some 0)).val, (v (some 1)).val, (v (some 2)).val, (v (some 3)).val]

@[reducible] private def r4d_findW (l : List ℕ) (tw : List (List (Fin 4))) (k : List ℕ) :
    List (Fin 4) :=
  match l, tw with
  | a :: l', w :: tw' => if k = r4d_key (r4d_dec a) then w else r4d_findW l' tw' k
  | _, _ => []

@[reducible] private def r4d_findR (l : List ℕ) (sp : List (List (List (Fin 4)))) (k : List ℕ) :
    List (List (Fin 4)) :=
  match l, sp with
  | a :: l', r :: sp' => if k = r4d_key (r4d_dec a) then r else r4d_findR l' sp' k
  | _, _ => []

@[reducible] private def r4d_mul (A B : Matrix N5 N5 (ZMod 3)) : Matrix N5 N5 (ZMod 3) :=
  Matrix.of fun i j => A i none * B none j + (A i (some 0) * B (some 0) j +
    A i (some 1) * B (some 1) j + A i (some 2) * B (some 2) j + A i (some 3) * B (some 3) j)

private theorem r4d_mul_eq (A B : Matrix N5 N5 (ZMod 3)) : r4d_mul A B = A * B := by
  ext i j
  show A i none * B none j + (A i (some 0) * B (some 0) j +
    A i (some 1) * B (some 1) j + A i (some 2) * B (some 2) j +
    A i (some 3) * B (some 3) j) = (A * B) i j
  rw [show (A * B) i j = ∑ k : N5, A i k * B k j from rfl, Fintype.sum_option,
    Fin.sum_univ_four]

@[reducible] private def r4d_dot (M : N5 → N5 → ZMod 3) (v : N5 → ZMod 3) (o : N5) : ZMod 3 :=
  M o none * v none + (M o (some 0) * v (some 0) + M o (some 1) * v (some 1) +
    M o (some 2) * v (some 2) + M o (some 3) * v (some 3))

private theorem r4d_dot_eq (M : Matrix N5 N5 (ZMod 3)) (v : N5 → ZMod 3) (o : N5) :
    (M.mulVec v) o = r4d_dot M v o := by
  show (∑ j : N5, M o j * v j) = r4d_dot M v o
  rw [Fintype.sum_option, Fin.sum_univ_four]

private theorem r4d_mulVec_fun (M : Matrix N5 N5 (ZMod 3)) (v : N5 → ZMod 3) :
    M.mulVec v = fun o => r4d_dot M v o := by
  funext o; rw [r4d_dot_eq]

@[reducible] private def r4d_wordprod (X : Matrix N5 N5 ℤ) (w : List (Fin 4)) :
    Matrix N5 N5 (ZMod 3) :=
  w.foldr (fun j M => r4d_mul (reflM X (some j)) M) 1

private theorem r4d_wordprod_eq (X : Matrix N5 N5 ℤ) (w : List (Fin 4)) :
    r4d_wordprod X w = List.prod (w.map (fun j => reflM X (some j))) := by
  induction w with
  | nil => rfl
  | cons j t ih =>
    show r4d_mul (reflM X (some j)) (r4d_wordprod X t) =
      reflM X (some j) * List.prod (List.map (fun j => reflM X (some j)) t)
    rw [r4d_mul_eq, ih]

private theorem r4d_wordprod_mem (X : Matrix N5 N5 ℤ) (b : Fin 4) (w : List (Fin 4))
    (hw : ∀ j ∈ w, j ≠ b) :
    r4d_wordprod X w ∈
      Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} => reflM X (some j.1)) := by
  rw [r4d_wordprod_eq]
  induction w with
  | nil => exact Submonoid.one_mem _
  | cons j t ih =>
    rw [List.map_cons, List.prod_cons]
    apply Submonoid.mul_mem
    · exact Submonoid.subset_closure ⟨⟨j, hw j (List.mem_cons_self ..)⟩, rfl⟩
    · exact ih (fun k hk => hw k (List.mem_cons_of_mem _ hk))

@[reducible] private def r4d_orbAt (l : List ℕ) (k : Fin 24) : N5 → ZMod 3 :=
  r4d_dec (l.getD k.val 0)

@[reducible] private def r4d_t (X : Matrix N5 N5 ℤ) (l : List ℕ) (tw : List (List (Fin 4)))
    (o : N5 → ZMod 3) : Matrix N5 N5 (ZMod 3) :=
  r4d_wordprod X (r4d_findW l tw (r4d_key o))

@[reducible] private def r4d_w (X : Matrix N5 N5 ℤ) (l : List ℕ)
    (sp : List (List (List (Fin 4)))) (o : N5 → ZMod 3) (i : Fin 4) :
    Matrix N5 N5 (ZMod 3) :=
  r4d_wordprod X ((r4d_findR l sp (r4d_key o)).getD i.val [])


@[reducible] private def r4d_good (X : Matrix N5 N5 ℤ) (b : Fin 4) (l : List ℕ)
    (tw : List (List (Fin 4))) (sp : List (List (List (Fin 4))))
    (wj : List (List (Fin 4))) (nx : Fin 24 → Fin 4 → Fin 24) : Prop :=
  (∀ o : N5, o ≠ some b →
      (fun a => r4d_dot (reflM X o) (r4d_orbAt l 0) a) = r4d_orbAt l 0) ∧
  (r4d_t X l tw (r4d_orbAt l 0) = 1) ∧
  (∀ k : Fin 24,
      (fun a => r4d_dot (r4d_t X l tw (r4d_orbAt l k)) (r4d_orbAt l 0) a) =
        r4d_orbAt l k) ∧
  (∀ k : Fin 24, ∀ i : Fin 4,
      r4d_orbAt l (nx k i) = fun a => r4d_dot (reflM X (some i)) (r4d_orbAt l k) a) ∧
  (∀ k : Fin 24, ∀ i : Fin 4,
      r4d_mul (reflM X (some i)) (r4d_t X l tw (r4d_orbAt l k)) =
        r4d_mul (r4d_t X l tw (r4d_orbAt l (nx k i)))
          (r4d_w X l sp (r4d_orbAt l k) i)) ∧
  (∀ k : Fin 24, ∀ i : Fin 4,
      ∀ j ∈ (r4d_findR l sp (r4d_key (r4d_orbAt l k))).getD i.val [], j ≠ b) ∧
  (∀ w ∈ wj, ∀ j ∈ w, j ≠ b) ∧
  ((wj.map (r4d_wordprod X)).Nodup) ∧
  (wj.length = 48) ∧
  ((1 : Matrix N5 N5 (ZMod 3)) ∈ wj.map (r4d_wordprod X)) ∧
  (∀ j : {j : Fin 4 // j ≠ b}, ∀ k : Fin (wj.map (r4d_wordprod X)).length,
      r4d_mul (reflM X (some j.1)) ((wj.map (r4d_wordprod X)).get k) ∈
        wj.map (r4d_wordprod X))

private theorem r4d_case_generic (X : Matrix N5 N5 ℤ) (b : Fin 4) (l : List ℕ)
    (tw : List (List (Fin 4))) (sp : List (List (List (Fin 4))))
    (wj : List (List (Fin 4))) (nx : Fin 24 → Fin 4 → Fin 24)
    (hf : r4d_good X b l tw sp wj nx) :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some b → (reflM X o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM X (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
          reflM X (some j.1))) ∧
      Nat.card (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
        reflM X (some j.1))) = 48 := by
  obtain ⟨hfix, hty, -, hnext, heq, hsch, hwj, hnodup, hlen, h1T, hcl⟩ := hf
  refine ⟨r4d_orbAt l 0, ?_, ?_, ?_⟩
  · intro o ho
    rw [r4d_mulVec_fun]
    exact hfix o ho
  · refine @monoid_schreier (Matrix N5 N5 (ZMod 3)) (N5 → ZMod 3) _
      { smul := fun M v => M.mulVec v
        one_smul := fun v => Matrix.one_mulVec v
        mul_smul := fun s g v => (Matrix.mulVec_mulVec v s g).symm }
      (Set.range fun i : Fin 4 => reflM X (some i))
      (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} => reflM X (some j.1)))
      (r4d_orbAt l 0) (Set.range (fun k : Fin 24 => r4d_orbAt l k))
      (r4d_t X l tw) ?_ ?_ ?_
    · exact hty
    · exact ⟨0, rfl⟩
    · intro o ho s hs
      obtain ⟨k, rfl⟩ := ho
      obtain ⟨i, rfl⟩ := hs
      refine ⟨?_, r4d_w X l sp (r4d_orbAt l k) i, r4d_wordprod_mem X b _ (hsch k i), ?_⟩
      · change (reflM X (some i)).mulVec (r4d_orbAt l k) ∈
          Set.range (fun k' : Fin 24 => r4d_orbAt l k')
        rw [r4d_mulVec_fun]
        exact ⟨nx k i, hnext k i⟩
      · change reflM X (some i) * r4d_t X l tw (r4d_orbAt l k) =
          r4d_t X l tw ((reflM X (some i)).mulVec (r4d_orbAt l k)) *
            r4d_w X l sp (r4d_orbAt l k) i
        rw [r4d_mulVec_fun, ← hnext k i, ← r4d_mul_eq, ← r4d_mul_eq]
        exact heq k i
  · have hWT : (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
        reflM X (some j.1)) : Set (Matrix N5 N5 (ZMod 3))) ⊆
        ((wj.map (r4d_wordprod X)).toFinset : Set (Matrix N5 N5 (ZMod 3))) := by
      intro g hg
      induction hg using Submonoid.closure_induction_left with
      | one => exact List.mem_toFinset.mpr h1T
      | mul_left s hs g hg ih =>
        obtain ⟨j, rfl⟩ := hs
        obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp ih)
        rw [← hk, ← r4d_mul_eq]
        exact List.mem_toFinset.mpr (hcl j k)
    have hTW : ((wj.map (r4d_wordprod X)).toFinset : Set (Matrix N5 N5 (ZMod 3))) ⊆
        (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
        reflM X (some j.1)) : Set (Matrix N5 N5 (ZMod 3))) := by
      intro g hg
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hg)
      exact r4d_wordprod_mem X b w (hwj w hw)
    have hset : (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
        reflM X (some j.1)) : Set (Matrix N5 N5 (ZMod 3))) =
        ((wj.map (r4d_wordprod X)).toFinset : Set (Matrix N5 N5 (ZMod 3))) :=
      Set.Subset.antisymm hWT hTW
    have hcardT : (wj.map (r4d_wordprod X)).toFinset.card = 48 := by
      rw [List.toFinset_card_of_nodup hnodup, List.length_map]
      exact hlen
    have e : Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
        reflM X (some j.1)) ≃
        ↥((wj.map (r4d_wordprod X)).toFinset : Set (Matrix N5 N5 (ZMod 3))) :=
      Equiv.subtypeEquivRight (fun x => by
        show x ∈ (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ b} =>
          reflM X (some j.1)) : Set (Matrix N5 N5 (ZMod 3))) ↔
          x ∈ ((wj.map (r4d_wordprod X)).toFinset : Set (Matrix N5 N5 (ZMod 3)))
        rw [hset])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    exact (Fintype.card_coe (wj.map (r4d_wordprod X)).toFinset).trans hcardT

@[reducible] private def r4d_tw_b0 : List (List (Fin 4)) :=
  [[], [0], [1, 0], [2, 1, 0], [1, 2, 1, 0], [3, 2, 1, 0], [0, 1, 2, 1, 0], [3, 1, 2, 1, 0], [3, 
  0, 1, 2, 1, 0], [2, 3, 1, 2, 1, 0], [2, 3, 0, 1, 2, 1, 0], [1, 2, 3, 1, 2, 1, 0], [1, 2, 3, 0, 
  1, 2, 1, 0], [0, 1, 2, 3, 1, 2, 1, 0], [0, 1, 2, 3, 0, 1, 2, 1, 0], [2, 1, 2, 3, 0, 1, 2, 1, 0], 
  [2, 0, 1, 2, 3, 0, 1, 2, 1, 0], [3, 2, 1, 2, 3, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 
  0], [3, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0], [3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0], [2, 3, 1, 2, 0, 1, 
  2, 3, 0, 1, 2, 1, 0], [1, 2, 3, 1, 2, 0, 1, 2, 3, 0, 1, 2, 1, 0], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3, 
  0, 1, 2, 1, 0]]

@[reducible] private def r4d_sp_b0 : List (List (List (Fin 4))) :=
  [[[], [1], [2], [3]], [[], [], [2], [3]], [[1], [], [], [3]], [[1], [], [], []], [[], [], [2], 
  []], [[1], [], [3], []], [[], [1], [2], []], [[], [], [], []], [[], [1], [], []], [[], [], [], 
  [2]], [[], [], [], [2]], [[], [], [3], [2]], [[], [], [], [2]], [[], [], [3], [2]], [[], [], [], 
  [2]], [[], [1], [], []], [[], [], [], []], [[], [1], [2], []], [[1], [], [3], []], [[], [], [2], 
  []], [[1], [], [], []], [[1], [], [], [3]], [[], [], [2], [3]], [[], [1], [2], [3]]]

@[reducible] private def r4d_wj_b0 : List (List (Fin 4)) :=
  [[], [1], [2], [3], [2, 1], [3, 1], [1, 2], [3, 2], [2, 3], [1, 2, 1], [3, 2, 1], [2, 3, 1], [2, 
  1, 2], [3, 1, 2], [2, 3, 2], [1, 2, 3], [2, 1, 2, 1], [3, 1, 2, 1], [2, 3, 2, 1], [1, 2, 3, 1], 
  [3, 2, 1, 2], [2, 3, 1, 2], [1, 2, 3, 2], [2, 1, 2, 3], [3, 2, 1, 2, 1], [2, 3, 1, 2, 1], [1, 2, 
  3, 2, 1], [2, 1, 2, 3, 1], [2, 3, 2, 1, 2], [1, 2, 3, 1, 2], [2, 1, 2, 3, 2], [3, 2, 1, 2, 3], 
  [2, 3, 2, 1, 2, 1], [1, 2, 3, 1, 2, 1], [2, 1, 2, 3, 2, 1], [3, 2, 1, 2, 3, 1], [1, 2, 3, 2, 1, 
  2], [2, 1, 2, 3, 1, 2], [3, 2, 1, 2, 3, 2], [1, 2, 3, 2, 1, 2, 1], [2, 1, 2, 3, 1, 2, 1], [3, 2, 
  1, 2, 3, 2, 1], [2, 1, 2, 3, 2, 1, 2], [3, 2, 1, 2, 3, 1, 2], [2, 1, 2, 3, 2, 1, 2, 1], [3, 2, 
  1, 2, 3, 1, 2, 1], [3, 2, 1, 2, 3, 2, 1, 2], [3, 2, 1, 2, 3, 2, 1, 2, 1]]

@[reducible] private def r4d_tw_b3 : List (List (Fin 4)) :=
  [[], [3], [2, 3], [1, 2, 3], [0, 1, 2, 3], [2, 1, 2, 3], [2, 0, 1, 2, 3], [3, 2, 1, 2, 3], [1, 
  2, 0, 1, 2, 3], [3, 2, 0, 1, 2, 3], [2, 1, 2, 0, 1, 2, 3], [3, 1, 2, 0, 1, 2, 3], [3, 2, 1, 2, 
  0, 1, 2, 3], [2, 3, 1, 2, 0, 1, 2, 3], [2, 3, 2, 1, 2, 0, 1, 2, 3], [1, 2, 3, 1, 2, 0, 1, 2, 3], 
  [1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [0, 1, 2, 3, 1, 2, 0, 1, 2, 3], [0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 
  3], [2, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [1, 2, 0, 1, 2, 3, 
  2, 1, 2, 0, 1, 2, 3], [2, 1, 2, 0, 1, 2, 3, 2, 1, 2, 0, 1, 2, 3], [3, 2, 1, 2, 0, 1, 2, 3, 2, 1, 
  2, 0, 1, 2, 3]]

@[reducible] private def r4d_sp_b3 : List (List (List (Fin 4))) :=
  [[[0], [1], [2], []], [[0], [1], [], []], [[0], [], [], [2]], [[], [], [], [2]], [[], [0], [], 
  [2]], [[], [1], [], []], [[], [], [], []], [[], [1], [2], []], [[1], [], [], []], [[], [], [2], 
  []], [[1], [0], [], []], [[1], [], [], []], [[1], [0], [], []], [[1], [], [], []], [[1], [], [], 
  []], [[], [], [2], []], [[], [], [], []], [[], [1], [2], []], [[], [1], [], []], [[], [0], [], 
  [2]], [[], [], [], [2]], [[0], [], [], [2]], [[0], [1], [], []], [[0], [1], [2], []]]

@[reducible] private def r4d_wj_b3 : List (List (Fin 4)) :=
  [[], [0], [1], [2], [1, 0], [2, 0], [0, 1], [2, 1], [1, 2], [0, 1, 0], [2, 1, 0], [1, 2, 0], [2, 
  0, 1], [1, 2, 1], [0, 1, 2], [2, 1, 2], [2, 0, 1, 0], [1, 2, 1, 0], [0, 1, 2, 0], [2, 1, 2, 0], 
  [1, 2, 0, 1], [0, 1, 2, 1], [2, 1, 2, 1], [2, 0, 1, 2], [1, 2, 0, 1, 0], [0, 1, 2, 1, 0], [2, 1, 
  2, 1, 0], [2, 0, 1, 2, 0], [0, 1, 2, 0, 1], [2, 1, 2, 0, 1], [2, 0, 1, 2, 1], [1, 2, 0, 1, 2], 
  [0, 1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 0], [2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0], [2, 0, 1, 2, 0, 
  1], [1, 2, 0, 1, 2, 1], [2, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 1, 0], [2, 1, 
  2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1, 0], [2, 1, 
  2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1, 0]]

@[reducible] private def r4d_orb_tt : List ℕ :=
  [64, 65, 68, 77, 80, 23, 78, 26, 24, 8, 6, 2, 3, 1, 4, 12, 13, 39, 16, 40, 43, 52, 46, 47]

@[reducible] private def r4d_nx_tt : Fin 24 → Fin 4 → Fin 24 :=
  ![![1, 0, 0, 0], ![0, 2, 1, 1], ![2, 1, 3, 2], ![3, 4, 2, 5], ![6, 3, 4, 7], ![5, 7, 5, 3], ![4, 
  6, 6, 8], ![8, 5, 9, 4], ![7, 8, 10, 6], ![10, 11, 7, 9], ![9, 12, 8, 10], ![13, 9, 11, 11], 
  ![14, 10, 15, 12], ![11, 14, 13, 13], ![12, 13, 16, 14], ![16, 15, 12, 17], ![15, 18, 14, 19], 
  ![19, 17, 17, 15], ![18, 16, 18, 20], ![17, 20, 19, 16], ![20, 19, 21, 18], ![21, 22, 20, 21], 
  ![23, 21, 22, 22], ![22, 23, 23, 23]]

private theorem r4d_case_tt :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some (caseB true) → (reflM (caseX true true) o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM (caseX true true) (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB true} =>
          reflM (caseX true true) (some j.1))) ∧
      Nat.card (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB true} =>
        reflM (caseX true true) (some j.1))) = 48 := by
  have hf : r4d_good (caseX true true) (caseB true) r4d_orb_tt r4d_tw_b0 r4d_sp_b0
      r4d_wj_b0 r4d_nx_tt := by
    decide +kernel
  exact r4d_case_generic (caseX true true) (caseB true) r4d_orb_tt r4d_tw_b0 r4d_sp_b0
    r4d_wj_b0 r4d_nx_tt hf

@[reducible] private def r4d_orb_tf : List ℕ :=
  [34, 61, 70, 67, 66, 76, 75, 22, 72, 21, 54, 18, 27, 9, 36, 15, 42, 17, 44, 51, 53, 50, 32, 59]

@[reducible] private def r4d_nx_tf : Fin 24 → Fin 4 → Fin 24 :=
  ![![0, 0, 0, 1], ![1, 1, 2, 0], ![2, 3, 1, 2], ![4, 2, 5, 3], ![3, 4, 6, 4], ![6, 5, 3, 7], ![5, 
  8, 4, 9], ![9, 7, 7, 5], ![8, 6, 10, 11], ![7, 11, 9, 6], ![10, 10, 8, 12], ![11, 9, 13, 8], 
  ![12, 12, 14, 10], ![13, 15, 11, 14], ![14, 16, 12, 13], ![17, 13, 15, 16], ![18, 14, 19, 15], 
  ![15, 17, 17, 18], ![16, 18, 20, 17], ![20, 19, 16, 19], ![19, 21, 18, 20], ![21, 20, 22, 21], 
  ![22, 22, 21, 23], ![23, 23, 23, 22]]

private theorem r4d_case_tf :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some (caseB false) → (reflM (caseX true false) o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM (caseX true false) (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB false} =>
          reflM (caseX true false) (some j.1))) ∧
      Nat.card (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB false} =>
        reflM (caseX true false) (some j.1))) = 48 := by
  have hf : r4d_good (caseX true false) (caseB false) r4d_orb_tf r4d_tw_b3 r4d_sp_b3
      r4d_wj_b3 r4d_nx_tf := by
    decide +kernel
  exact r4d_case_generic (caseX true false) (caseB false) r4d_orb_tf r4d_tw_b3 r4d_sp_b3
    r4d_wj_b3 r4d_nx_tf hf

@[reducible] private def r4d_orb_ft : List ℕ :=
  [46, 47, 50, 41, 44, 14, 42, 17, 15, 8, 6, 2, 3, 1, 4, 21, 22, 75, 25, 76, 79, 70, 64, 65]

@[reducible] private def r4d_nx_ft : Fin 24 → Fin 4 → Fin 24 :=
  ![![1, 0, 0, 0], ![0, 2, 1, 1], ![2, 1, 3, 2], ![3, 4, 2, 5], ![6, 3, 4, 7], ![5, 7, 5, 3], ![4, 
  6, 6, 8], ![8, 5, 9, 4], ![7, 8, 10, 6], ![10, 11, 7, 9], ![9, 12, 8, 10], ![13, 9, 11, 11], 
  ![14, 10, 15, 12], ![11, 14, 13, 13], ![12, 13, 16, 14], ![16, 15, 12, 17], ![15, 18, 14, 19], 
  ![19, 17, 17, 15], ![18, 16, 18, 20], ![17, 20, 19, 16], ![20, 19, 21, 18], ![21, 22, 20, 21], 
  ![23, 21, 22, 22], ![22, 23, 23, 23]]

private theorem r4d_case_ft :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some (caseB true) → (reflM (caseX false true) o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM (caseX false true) (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB true} =>
          reflM (caseX false true) (some j.1))) ∧
      Nat.card (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB true} =>
        reflM (caseX false true) (some j.1))) = 48 := by
  have hf : r4d_good (caseX false true) (caseB true) r4d_orb_ft r4d_tw_b0 r4d_sp_b0
      r4d_wj_b0 r4d_nx_ft := by
    decide +kernel
  exact r4d_case_generic (caseX false true) (caseB true) r4d_orb_ft r4d_tw_b0 r4d_sp_b0
    r4d_wj_b0 r4d_nx_ft hf

@[reducible] private def r4d_orb_ff : List ℕ :=
  [61, 34, 52, 49, 48, 40, 39, 13, 36, 12, 27, 9, 54, 18, 72, 24, 78, 26, 80, 69, 71, 68, 59, 32]

@[reducible] private def r4d_nx_ff : Fin 24 → Fin 4 → Fin 24 :=
  ![![0, 0, 0, 1], ![1, 1, 2, 0], ![2, 3, 1, 2], ![4, 2, 5, 3], ![3, 4, 6, 4], ![6, 5, 3, 7], ![5, 
  8, 4, 9], ![9, 7, 7, 5], ![8, 6, 10, 11], ![7, 11, 9, 6], ![10, 10, 8, 12], ![11, 9, 13, 8], 
  ![12, 12, 14, 10], ![13, 15, 11, 14], ![14, 16, 12, 13], ![17, 13, 15, 16], ![18, 14, 19, 15], 
  ![15, 17, 17, 18], ![16, 18, 20, 17], ![20, 19, 16, 19], ![19, 21, 18, 20], ![21, 20, 22, 21], 
  ![22, 22, 21, 23], ![23, 23, 23, 22]]

private theorem r4d_case_ff :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some (caseB false) → (reflM (caseX false false) o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM (caseX false false) (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB false} =>
          reflM (caseX false false) (some j.1))) ∧
      Nat.card (Submonoid.closure (Set.range fun j : {j : Fin 4 // j ≠ caseB false} =>
        reflM (caseX false false) (some j.1))) = 48 := by
  have hf : r4d_good (caseX false false) (caseB false) r4d_orb_ff r4d_tw_b3 r4d_sp_b3
      r4d_wj_b3 r4d_nx_ff := by
    decide +kernel
  exact r4d_case_generic (caseX false false) (caseB false) r4d_orb_ff r4d_tw_b3 r4d_sp_b3
    r4d_wj_b3 r4d_nx_ff hf

theorem r4j_fin_case (ori cell : Bool) :
    ∃ y : N5 → ZMod 3,
      (∀ o : N5, o ≠ some (caseB cell) → (reflM (caseX ori cell) o).mulVec y = y) ∧
      (∀ g ∈ Submonoid.closure (Set.range fun i : Fin 4 => reflM (caseX ori cell) (some i)),
        g.mulVec y = y →
        g ∈ Submonoid.closure
          (Set.range fun j : {j : Fin 4 // j ≠ caseB cell} => reflM (caseX ori cell) (some j.1))) ∧
      Nat.card (Submonoid.closure
        (Set.range fun j : {j : Fin 4 // j ≠ caseB cell} =>
          reflM (caseX ori cell) (some j.1))) = 48 := by
  cases ori <;> cases cell <;>
  first
    | exact r4d_case_tt
    | exact r4d_case_tf
    | exact r4d_case_ft
    | exact r4d_case_ff

end R4J

end CFSG.StandardType

end
