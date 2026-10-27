module

public import CFSG.Sporadic.Co2Smith.Generators
public import CFSG.Sporadic.Co2Smith.SeedValidCheck

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem validM_iff {X : Array ℕ} :
    Native.validM X = true ↔ X.size = 22 ∧ ∀ (i : ℕ) (h : i < X.size), X[i] < 4194304 := by
  simp only [Native.validM, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]

theorem vecMulN_lt {Y : Array ℕ} (hY : ∀ (i : ℕ) (h : i < Y.size), Y[i] < 4194304) (v : ℕ) :
    vecMulN 22 Y v < 4194304 := by
  rw [vecMulN]
  have key : ∀ (L : List ℕ) (acc : ℕ), acc < 4194304 →
      L.foldl (fun acc j => if v.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc <
        4194304 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih =>
      intro acc h
      apply ih
      dsimp only
      split_ifs
      · have h' : acc < 2 ^ 22 := h
        refine Nat.xor_lt_two_pow h' ?_
        cases hj : Y[j]? with
        | none => simp
        | some x =>
          rw [Option.getD_some]
          obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hj
          exact hY j hlt
      · exact h
  exact key _ 0 (by norm_num)

theorem validM_mulRows {X Y : Array ℕ} (hX : Native.validM X = true)
    (hY : Native.validM Y = true) : Native.validM (mulRows 22 X Y) = true := by
  rw [validM_iff] at hX hY ⊢
  refine ⟨by rw [mulRows, Array.size_map, hX.1], fun i hi => ?_⟩
  simp only [mulRows, Array.getElem_map]
  exact vecMulN_lt hY.2 _

theorem validM_idRows : Native.validM (idRows 22) = true := by
  rw [validM_iff]
  refine ⟨by simp [idRows], fun i hi => ?_⟩
  simp only [idRows, Array.getElem_ofFn, Nat.one_shiftLeft]
  have hi' : i < 22 := by simpa [idRows] using hi
  exact (Nat.pow_lt_pow_right (by norm_num) hi').trans_le (by norm_num)

theorem validM_wRows {L : Array (Array ℕ)} : ∀ w : List ℕ,
    (∀ k ∈ w, Native.validM L[k]! = true) → Native.validM (Native.wRows L w) = true
  | [], _ => validM_idRows
  | k :: w, hw => validM_mulRows (hw k List.mem_cons_self)
      (validM_wRows w fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem validM_seeds :
    ∀ k < 2, Native.validM seedRowsArr[k]! = true := by
  have h := seedsValid_check
  simp only [Native.seedsValidOK, Bool.and_eq_true] at h
  intro k hk
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact h.1
  · exact h.2

theorem aWord_lt : ∀ k ∈ Native.aWord, k < 2 := by decide +kernel

theorem bWord_lt : ∀ k ∈ Native.bWord, k < 2 := by decide +kernel

theorem validM_letters :
    ∀ k < 4, Native.validM (Native.letters seedRowsArr)[k]! = true := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact validM_seeds 0 (by norm_num)
  · exact validM_seeds 1 (by norm_num)
  · exact validM_wRows _ fun j hj => validM_seeds j (aWord_lt j hj)
  · exact validM_wRows _ fun j hj => validM_seeds j (bWord_lt j hj)

theorem validM_mRows {w : List ℕ} (hw : ∀ k ∈ w, k < 4) :
    Native.validM (Native.mRows seedRowsArr w) = true :=
  validM_wRows w fun k hk => validM_letters k (hw k hk)

theorem validM_hR
    {i : ℕ} (hi : i < 8) : Native.validM hR[i]! = true := by
  have e := hR_get ⟨i, hi⟩
  simp only at e
  rw [e]
  exact validM_mRows (hWords_lt i hi)

theorem validM_foldr (v : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < 8) →
    Native.validM (l.foldr (fun i acc => if v.testBit i then mulRows 22 hR[i]! acc else acc)
      (idRows 22)) = true
  | [], _ => validM_idRows
  | i :: l, hl => by
    rw [List.foldr_cons]
    have ih := validM_foldr v l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    split_ifs
    · exact validM_mulRows (validM_hR (hl i List.mem_cons_self)) ih
    · exact ih

theorem validM_nfRows
    (s v : ℕ) : Native.validM (Native.nfRows seedRowsArr hR s v) = true := by
  have h := validM_foldr v (List.range 8) fun i hi => List.mem_range.mp hi
  rw [Native.nfRows]
  split_ifs
  · exact validM_mulRows (validM_seeds 0 (by norm_num)) h
  · exact h

theorem commute_iff_commRows {u v : K} {X Y : Array ℕ} (hu : u.val.val = rowsMatrix 22 X)
    (hv : v.val.val = rowsMatrix 22 Y) (hX : Native.validM X = true)
    (hY : Native.validM Y = true) : u * v = v * u ↔ Native.commRows X Y = true := by
  refine ⟨fun h => ?_, comm_of_commRows hu hv⟩
  have hm : rowsMatrix 22 (mulRows 22 X Y) = rowsMatrix 22 (mulRows 22 Y X) := by
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hu, ← hv, ← val_val_mul, ← val_val_mul, h]
  rw [Native.commRows, beq_iff_eq]
  exact eq_of_rowsMatrix_eq (validM_mulRows hX hY) (validM_mulRows hY hX) hm

end CFSG.Sporadic.Co2Smith
