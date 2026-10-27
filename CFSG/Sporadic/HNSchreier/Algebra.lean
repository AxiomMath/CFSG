module

public import CFSG.Sporadic.HNSchreier.ModuleCheckInputs
public import CFSG.Sporadic.HNSchreier.Seeds
public import CFSG.LinearAlgebra.CorankOneSpanning

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native Matrix
open CFSG.LinearAlgebra

instance hns_fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable abbrev seedMat (l : ℕ) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  if l = 1 then matA else matB

theorem toMat_seedSel' {l : ℕ} (hl : l = 1 ∨ l = 2) :
    toMat 5 133 (seedSel rowsA rowsB l) = seedMat l := toMat_seedSel l hl

@[expose] noncomputable def matC : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  matB * matA * matB * matA + (3 : ZMod 5) • (matB * matA) + (2 : ZMod 5) • matB +
    (4 : ZMod 5) • (matA * matB * matB * matA) + matB * matB

theorem toMat_apply_133 (X : Array (Array ℕ)) (i j : Fin 133) :
    ((X[i.val]!)[j.val]! : ZMod 5) = toMat 5 133 X i j := rfl

theorem toMat_word_seed4 {a b c e : ℕ} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2)
    (hc : c = 1 ∨ c = 2) (he : e = 1 ∨ e = 2) :
    toMat 5 133 (wordM (seedSel rowsA rowsB) [a, b, c, e]) =
      seedMat a * seedMat b * seedMat c * seedMat e := by
  have hw : ∀ l ∈ [a, b, c, e], l = 1 ∨ l = 2 := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> assumption
  rw [toMat_wordM_seed _ hw]
  simp only [List.map_cons, List.map_nil, prod_cons_cons, List.prod_singleton, mul_assoc]

theorem toMat_word_seed2 {a b : ℕ} (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2) :
    toMat 5 133 (wordM (seedSel rowsA rowsB) [a, b]) = seedMat a * seedMat b := by
  have hw : ∀ l ∈ [a, b], l = 1 ∨ l = 2 := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> assumption
  rw [toMat_wordM_seed _ hw]
  simp only [List.map_cons, List.map_nil, prod_cons_cons, List.prod_singleton]

theorem seedMat_one : seedMat 1 = matA := by simp [seedMat]

theorem seedMat_two : seedMat 2 = matB := by simp [seedMat]

theorem toMat_cRows : toMat 5 133 (cRows rowsA rowsB) = matC := by
  have w1 := toMat_word_seed4 (a := 2) (b := 1) (c := 2) (e := 1) (by simp) (by simp) (by simp)
    (by simp)
  have w2 := toMat_word_seed2 (a := 2) (b := 1) (by simp) (by simp)
  have w4 := toMat_word_seed4 (a := 1) (b := 2) (c := 2) (e := 1) (by simp) (by simp) (by simp)
    (by simp)
  have w5 := toMat_word_seed2 (a := 2) (b := 2) (by simp) (by simp)
  simp only [seedMat_one, seedMat_two] at w1 w2 w4 w5
  ext i j
  have key : ((cRows rowsA rowsB)[i.val]!)[j.val]! =
      (((wordM (seedSel rowsA rowsB) [2, 1, 2, 1])[i.val]!)[j.val]! +
        3 * ((wordM (seedSel rowsA rowsB) [2, 1])[i.val]!)[j.val]! + 2 * (rowsB[i.val]!)[j.val]! +
        4 * ((wordM (seedSel rowsA rowsB) [1, 2, 2, 1])[i.val]!)[j.val]! +
        ((wordM (seedSel rowsA rowsB) [2, 2])[i.val]!)[j.val]!) % 5 := by
    unfold cRows
    rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
    rfl
  rw [toMat_apply, key, ZMod.natCast_mod]
  push_cast
  rw [toMat_apply_133 _ i j, toMat_apply_133 _ i j, toMat_apply_133 rowsB i j,
    toMat_apply_133 _ i j, toMat_apply_133 _ i j, w1, w2, w4, w5, toMat_rowsB, matC]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem matC_mem : matC ∈ Algebra.adjoin (ZMod 5) ({matA, matB} : Set _) := by
  have hA : matA ∈ Algebra.adjoin (ZMod 5) ({matA, matB} : Set _) :=
    Algebra.subset_adjoin (Set.mem_insert _ _)
  have hB : matB ∈ Algebra.adjoin (ZMod 5) ({matA, matB} : Set _) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  rw [matC]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hB hA) hB) hA
  · exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hB hA) _
  · exact Subalgebra.smul_mem _ hB _
  · exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ hA hB) hB) hA) _
  · exact Subalgebra.mul_mem _ hB hB

theorem toVec_zeroV : toVec 5 133 zeroV = 0 := by
  funext j
  rw [toVec_apply, zeroV, getElem!_pos _ _ (by simp)]
  simp

theorem toVec_ne_zero {w : Array ℕ} (hs : w.size = 133) (hlt : w.all (· < 5) = true)
    (hnz : w.any (· != 0) = true) : toVec 5 133 w ≠ 0 := by
  intro h
  rw [Array.any_eq_true] at hnz
  obtain ⟨j, hj, hne⟩ := hnz
  have e := congrFun h ⟨j, by omega⟩
  rw [toVec_apply, getElem!_pos w j hj, Pi.zero_apply] at e
  rw [Array.all_eq_true] at hlt
  have h5 := hlt j hj
  simp only [decide_eq_true_eq] at h5
  have : w[j] % 5 = 0 := by
    have := (ZMod.natCast_eq_natCast_iff' w[j] 0 5).1 (e.trans Nat.cast_zero.symm)
    simpa using this
  rw [Nat.mod_eq_of_lt h5] at this
  simp [this] at hne

noncomputable def recMat (recs : List (ℕ × ℕ))
    (upd : ℕ → Matrix (Fin 133) (Fin 133) (ZMod 5) → Matrix (Fin 133) (Fin 133) (ZMod 5)) :
    ℕ → ℕ → Matrix (Fin 133) (Fin 133) (ZMod 5)
  | 0, _ => 1
  | f + 1, i => if i = 0 then 1 else upd recs[i]!.2 (recMat recs upd f recs[i]!.1)

theorem recMat_mem (recs : List (ℕ × ℕ))
    (upd : ℕ → Matrix (Fin 133) (Fin 133) (ZMod 5) → Matrix (Fin 133) (Fin 133) (ZMod 5))
    (S : Set (Matrix (Fin 133) (Fin 133) (ZMod 5))) (h1 : 1 ∈ S)
    (hS : ∀ i, 0 < i → ∀ X ∈ S, upd recs[i]!.2 X ∈ S) : ∀ f i, recMat recs upd f i ∈ S := by
  intro f
  induction f with
  | zero => intro i; exact h1
  | succ f ih =>
    intro i
    rw [recMat]
    split_ifs with hi
    · exact h1
    · exact hS i (Nat.pos_of_ne_zero hi) _ (ih _)

theorem recOK_spec {w : Array ℕ} {step : ℕ → Array ℕ → Array ℕ} {recs : List (ℕ × ℕ)}
    {vs : Array (Array ℕ)} (h : recOK w step recs vs = true)
    (upd : ℕ → Matrix (Fin 133) (Fin 133) (ZMod 5) → Matrix (Fin 133) (Fin 133) (ZMod 5))
    (app : Matrix (Fin 133) (Fin 133) (ZMod 5) → Fin 133 → ZMod 5) (hw : app 1 = toVec 5 133 w)
    (hstep : ∀ l x X, (l = 1 ∨ l = 2) → toVec 5 133 x = app X →
      toVec 5 133 (step l x) = app (upd l X)) :
    (∀ i, 0 < i → i < 133 → recs[i]!.2 = 1 ∨ recs[i]!.2 = 2) ∧
      ∀ i < 133, toVec 5 133 vs[i]! = app (recMat recs upd 133 i) := by
  unfold recOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, h0⟩, hall⟩ := h
  have hrec : ∀ i, 0 < i → i < 133 → recs[i]!.1 < i ∧ (recs[i]!.2 = 1 ∨ recs[i]!.2 = 2) ∧
      vs[i]! = step recs[i]!.2 vs[recs[i]!.1]! := by
    intro i hi0 hi
    rcases hall i hi with h | h
    · omega
    · exact ⟨h.1.1, h.1.2, h.2⟩
  refine ⟨fun i hi0 hi => (hrec i hi0 hi).2.1, ?_⟩
  have key : ∀ i < 133, ∀ f, i < f → toVec 5 133 vs[i]! = app (recMat recs upd f i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi f hf
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [recMat]
      split_ifs with hi0
      · subst hi0
        rw [h0, hw]
      · obtain ⟨hj, hl, he⟩ := hrec i (Nat.pos_of_ne_zero hi0) hi
        rw [he]
        exact hstep _ _ _ hl (ih _ hj (by omega) f (by omega))
  exact fun i hi => key i hi 133 hi

theorem toMat_colsMat_eq_transpose (X : Array (Array ℕ)) :
    toMat 5 133 (colsMat 133 X) = (toMat 5 133 X)ᵀ := by
  ext i t
  rw [toMat_colsMat, Matrix.transpose_apply, toMat_apply, toVec_apply]

abbrev skipFin : Fin 132 → Fin 133 := Fin.succAbove 1

theorem toMat_minorRows (X : Array (Array ℕ)) :
    toMat 5 132 (minorRows X) = (toMat 5 133 X).submatrix skipFin skipFin := by
  ext i j
  rw [toMat_apply, Matrix.submatrix_apply, toMat_apply]
  unfold minorRows
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  have e : ∀ k : Fin 132, skipOne k.val = (skipFin k).val := by
    intro k
    simp only [skipOne, skipFin, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_one]
    split_ifs <;> simp
  rw [e i, e j]

theorem isUnit_of_mulM_eq {d : ℕ} {X Y : Array (Array ℕ)} (h : mulM 5 d X Y = idM d) :
    IsUnit (toMat 5 d X) := by
  have e := congrArg (toMat 5 d) h
  rw [toMat_mulM, toMat_idM] at e
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)

theorem rank_le_of_col_zero {m k : ℕ} (N : Matrix (Fin m) (Fin (k + 1)) (ZMod 5))
    (h : ∀ i, N i 0 = 0) : N.rank ≤ k := by
  classical
  let E : Matrix (Fin k) (Fin (k + 1)) (ZMod 5) := fun a j => if j = a.succ then 1 else 0
  have hN : N = N.submatrix id Fin.succ * E := by
    ext i j
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ (fun b => ?_) j
    · simp [E, h i, (Fin.succ_ne_zero _).symm]
    · simp [E, Fin.succ_inj]
  rw [hN]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  have := Matrix.rank_le_card_width (N.submatrix id Fin.succ)
  simpa using this

end CFSG.Sporadic.HNSchreier
