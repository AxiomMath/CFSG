module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyMat
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)

abbrev Mat := Array V4

@[expose] def powRows (M : Mat) : ℕ → Mat
  | 0 => idRows
  | e + 1 => mulRows (powRows M e) M

theorem rowsMatrix_powRows (M : Mat) (e : ℕ) :
    rowsMatrix (powRows M e) = rowsMatrix M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact rowsMatrix_idRows
  | succ e ih => rw [powRows, rowsMatrix_mulRows, ih, pow_succ]

@[expose] def powL (M : Mat) (e : ℕ) : Mat := if e = 1 then M else powRows M e

theorem rowsMatrix_powL (M : Mat) (e : ℕ) : rowsMatrix (powL M e) = rowsMatrix M ^ e := by
  unfold powL
  split_ifs with h
  · subst h
    rw [pow_one]
  · exact rowsMatrix_powRows M e

@[expose] def evalWord (gs : Array Mat) (w : List (ℕ × ℕ)) : Mat :=
  w.foldl (fun acc x => mulRows acc (powL gs[x.1]! x.2)) idRows

theorem rowsMatrix_evalWord (gs : Array Mat) (w : List (ℕ × ℕ)) :
    rowsMatrix (evalWord gs w) = (w.map fun x => rowsMatrix gs[x.1]! ^ x.2).prod := by
  have key : ∀ (w : List (ℕ × ℕ)) (acc : Mat),
      rowsMatrix (w.foldl (fun acc x => mulRows acc (powL gs[x.1]! x.2)) acc) =
        rowsMatrix acc * (w.map fun x => rowsMatrix gs[x.1]! ^ x.2).prod := by
    intro w
    induction w with
    | nil => intro acc; simp
    | cons x w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, rowsMatrix_powL, List.map_cons,
        List.prod_cons, mul_assoc]
  rw [evalWord, key, rowsMatrix_idRows, one_mul]

@[expose, reducible] def Rp (M : Mat) (g : GL (Fin 248) (ZMod 2)) : Prop :=
  rowsMatrix M = (g : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem Rp.mul {X Y : Mat} {g h : GL (Fin 248) (ZMod 2)} (hX : Rp X g) (hY : Rp Y h) :
    Rp (mulRows X Y) (g * h) := by
  unfold Rp at *
  rw [rowsMatrix_mulRows, hX, hY, Units.val_mul]

theorem Rp.eq_of_eq {X Y : Mat} {g h : GL (Fin 248) (ZMod 2)} (hX : Rp X g) (hY : Rp Y h)
    (e : X = Y) : g = h := by
  subst e
  exact Units.ext (hX.symm.trans hY)

theorem rowsMatrix_evalWord_eq {gs : Array Mat} {g : ℕ → GL (Fin 248) (ZMod 2)}
    {w : List (ℕ × ℕ)} (h : ∀ x ∈ w, Rp gs[x.1]! (g x.1)) :
    Rp (evalWord gs w) (wordG g w) := by
  unfold Rp
  rw [rowsMatrix_evalWord, wordG]
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Units.val_mul,
      Units.val_pow_eq_pow_val, h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

@[expose] def pcCheck (n : ℕ) (P : Array Mat) (cubeW : Array (List (ℕ × ℕ)))
    (commW : Array (Array (List (ℕ × ℕ)))) : Bool :=
  decide (P.size = n) && (List.range n).all (fun i =>
    (cubeW[i]!).all (fun x => decide (i < x.1 ∧ x.1 < n)) &&
      (evalWord P [(i, 3)] == evalWord P cubeW[i]!) &&
      (List.range n).all (fun j => decide (j ≤ i) ||
        (((commW[i]!)[j]!).all (fun x => decide (i < x.1 ∧ x.1 < n)) &&
          (evalWord P [(i, 1), (j, 1)] == evalWord P ((commW[i]!)[j]! ++ [(i, 1)])))))

theorem pcCheck_size {n : ℕ} {P : Array Mat} {cubeW : Array (List (ℕ × ℕ))}
    {commW : Array (Array (List (ℕ × ℕ)))} (h : pcCheck n P cubeW commW = true) : P.size = n := by
  simp only [pcCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem pc_sound {n : ℕ} {P : Array Mat} {cubeW : Array (List (ℕ × ℕ))}
    {commW : Array (Array (List (ℕ × ℕ)))} {g : ℕ → GL (Fin 248) (ZMod 2)}
    (hg : ∀ l < n, Rp P[l]! (g l)) (h : pcCheck n P cubeW commW = true) :
    (∀ i < n, g i ^ 3 ∈ tailGroup g n (i + 1)) ∧
      ∀ i < n, ∀ j, i < j → j < n → g i * g j * (g i)⁻¹ ∈ tailGroup g n (i + 1) := by
  simp only [pcCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hsize, h⟩ := h
  have hword : ∀ w : List (ℕ × ℕ), (∀ x ∈ w, x.1 < n) →
      Rp (evalWord P w) (wordG g w) := fun w hw =>
    rowsMatrix_evalWord_eq fun x hx => hg x.1 (hw x hx)
  have hmem : ∀ i, ∀ w : List (ℕ × ℕ), (∀ x ∈ w, i < x.1 ∧ x.1 < n) →
      wordG g w ∈ tailGroup g n (i + 1) := by
    intro i w hw
    refine wordG_mem fun x hx => ?_
    exact Subgroup.subset_closure ⟨x.1, ⟨(hw x hx).1, (hw x hx).2⟩, rfl⟩
  refine ⟨fun i hi => ?_, fun i hi j hij hjn => ?_⟩
  · obtain ⟨⟨hl, he⟩, -⟩ := h i hi
    have hl' : ∀ x ∈ cubeW[i]!, i < x.1 ∧ x.1 < n := hl
    have hrep := hword cubeW[i]! fun x hx => (hl' x hx).2
    have hrep3 := hword [(i, 3)] (by simpa using hi)
    have := hrep3.eq_of_eq hrep (beq_iff_eq.1 he)
    have e3 : wordG g [(i, 3)] = g i ^ 3 := by simp [wordG]
    rw [e3] at this
    rw [this]
    exact hmem i _ hl'
  · obtain ⟨-, h2⟩ := h i hi
    have h3 := h2 j hjn
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true] at h3
    rcases h3 with h3 | ⟨hl, he⟩
    · omega
    · have hl' : ∀ x ∈ (commW[i]!)[j]!, i < x.1 ∧ x.1 < n := hl
      have hrep := hword ((commW[i]!)[j]! ++ [(i, 1)]) (by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact (hl' x hx).2
        · simp only [List.mem_singleton] at hx
          rw [hx]
          exact hi)
      have hrep2 := hword [(i, 1), (j, 1)] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact hjn)
      have := hrep2.eq_of_eq hrep (beq_iff_eq.1 he)
      have e2 : wordG g [(i, 1), (j, 1)] = g i * g j := by simp [wordG]
      have e3 : wordG g ((commW[i]!)[j]! ++ [(i, 1)]) =
          wordG g (commW[i]!)[j]! * g i := by simp [wordG, List.map_append, List.prod_append]
      rw [e2, e3] at this
      rw [this, mul_inv_cancel_right]
      exact hmem i _ hl'

end CFSG.RankThree.PartTwo.Sec4.Item434SporTh
