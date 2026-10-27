module

public import CFSG.Monster.B.E6.StdF4RadicalRoots

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4

theorem par_nil {C : ℕ → ℕ → Bool} (u : ℕ → Bool) (j : ℕ) : par C [] u j = false := rfl

theorem parAfter_append_singleton {C : ℕ → ℕ → Bool} (u : ℕ → Bool) {j : ℕ} :
    ∀ {L : List ℕ}, j ∉ L → parAfter C (L ++ [j]) u j = false
  | [], _ => by simp [parAfter, par_nil]
  | i :: L, h => by
    have hij : i ≠ j := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, parAfter, ite_eq_right hij]
    exact parAfter_append_singleton u (fun hj => h (List.mem_cons_of_mem _ hj))

theorem testBit_xor_shiftLeft (m j : ℕ) :
    (fun i => (m ^^^ (1 <<< j)).testBit i) =
      Function.update (fun i => m.testBit i) j (!m.testBit j) := by
  funext i
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · rw [Function.update_of_ne h, decide_eq_false (Ne.symm h), Bool.xor_false]

@[expose] def nfM
    (m : ℕ) : ModGL Tag.E6 K := lprod xr (List.range 21) fun i => m.testBit i

@[expose] def stepM (m j : ℕ) : ℕ :=
  if parAfter cC (List.range 21) (fun i => m.testBit i) j then m ^^^ (1 <<< j) ^^^ (1 <<< 20)
  else m ^^^ (1 <<< j)

@[expose] def nfWM (w : List ℕ) : ℕ := w.foldl stepM 0

@[expose] def evalW
    (w : List ℕ) : ModGL Tag.E6 K := (w.map xr).prod

theorem evalW_nil : evalW [] = 1 := rfl

theorem evalW_cons
    (j : ℕ) (w : List ℕ) : evalW (j :: w) = xr j * evalW w := rfl

theorem evalW_append
    (w w' : List ℕ) : evalW (w ++ w') = evalW w * evalW w' := by
  simp [evalW, List.map_append, List.prod_append]

theorem evalW_singleton
    (j : ℕ) : evalW [j] = xr j := by simp [evalW]

theorem nfM_zero : nfM 0 = 1 := by
  simp only [nfM, lprod, Nat.zero_testBit, Bool.false_eq_true, ite_false]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    rfl

theorem mem_range_21 {j : ℕ} (hj : j < 21) : j ∈ List.range 21 := List.mem_range.2 hj

theorem nfM_mul_xr
    (m : ℕ) {j : ℕ} (hj : j < 21) : nfM m * xr j = nfM (stepM m j) := by
  have hsub : ∀ i ∈ List.range 21, i ∈ List.range 21 := fun i hi => hi
  rw [nfM, lprod_mul_x_of_mem rels_xr (mem_range_21 hj) _ List.nodup_range (mem_range_21 hj) hsub,
    ← testBit_xor_shiftLeft, stepM]
  split_ifs with hp
  · rw [hp, zb_true, ← xr_twenty,
      lprod_mul_x_of_mem rels_xr (mem_range_21 (by norm_num)) _ List.nodup_range
        (mem_range_21 (by norm_num)) hsub, ← testBit_xor_shiftLeft]
    have h20 : parAfter cC (List.range 21) (fun i => (m ^^^ 1 <<< j).testBit i) 20 = false := by
      rw [List.range_succ]
      exact parAfter_append_singleton _ (by simp)
    rw [h20, zb_false, mul_one, nfM]
  · rw [Bool.not_eq_true] at hp
    rw [hp, zb_false, mul_one, nfM]

theorem nfM_mul_evalW
    (w : List ℕ) (hw : ∀ j ∈ w, j < 21) (m : ℕ) :
    nfM m * evalW w = nfM (w.foldl stepM m) := by
  induction w generalizing m with
  | nil => rw [evalW_nil, mul_one, List.foldl_nil]
  | cons j w ih =>
    rw [evalW_cons, ← mul_assoc, nfM_mul_xr m (hw j (List.mem_cons_self ..)),
      ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)), List.foldl_cons]

theorem evalW_eq_nfM
    (w : List ℕ) (hw : ∀ j ∈ w, j < 21) : evalW w = nfM (nfWM w) := by
  rw [nfWM, ← nfM_mul_evalW w hw, nfM_zero, one_mul]

theorem evalW_eq_of_nfWM_eq
    {w w' : List ℕ} (hw : ∀ j ∈ w, j < 21) (hw' : ∀ j ∈ w', j < 21)
    (h : nfWM w = nfWM w') : evalW w = evalW w' := by
  rw [evalW_eq_nfM w hw, evalW_eq_nfM w' hw', h]

@[expose] def qr
    (i : ℕ) : ModGL Tag.E6 K := evalW (orbIdx i)

@[expose] def bRows : List ℕ := [8192, 4096, 0, 0, 1024, 0, 512, 0, 0, 64, 16, 0, 2, 1, 0]

@[expose] def bC (i j : ℕ) : Bool := (bRows.getD j 0).testBit i

theorem orbIdx_lt {i : ℕ} (hi : i < 15) : ∀ k ∈ orbIdx i, k < 21 := by
  have h : (List.range 15).all (fun i => (orbIdx i).all fun k => decide (k < 21)) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi

theorem relCheck : (List.range 15).all (fun i => (List.range 15).all fun j =>
    nfWM (orbIdx i ++ orbIdx j) == nfWM (orbIdx j ++ orbIdx i ++ if bC i j then [20] else [])) =
    true := by decide +kernel

theorem sqCheck : (List.range 15).all (fun i => nfWM (orbIdx i ++ orbIdx i) == 0) = true := by
  decide +kernel

theorem bC_fourteen : (List.range 15).all (fun i => !bC 14 i && !bC i 14) = true := by
  decide +kernel

theorem qr_fourteen :
    qr 14 = rootInvM := by
  rw [qr, show orbIdx 14 = [20] from rfl, evalW_singleton, xr_twenty]

theorem qr_mul_qr
    {i j : ℕ} (hi : i < 15) (hj : j < 15) :
    qr i * qr j = qr j * qr i * zb rootInvM (bC i j) := by
  have h := relCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hw : ∀ k ∈ orbIdx i ++ orbIdx j, k < 21 := fun k hk => by
    rcases List.mem_append.1 hk with hk | hk
    exacts [orbIdx_lt hi k hk, orbIdx_lt hj k hk]
  have hw' : ∀ k ∈ orbIdx j ++ orbIdx i ++ (if bC i j then [20] else []), k < 21 := fun k hk => by
    rcases List.mem_append.1 hk with hk | hk
    · rcases List.mem_append.1 hk with hk | hk
      exacts [orbIdx_lt hj k hk, orbIdx_lt hi k hk]
    · split_ifs at hk
      · rw [List.mem_singleton.1 hk]
        norm_num
      · exact absurd hk (List.not_mem_nil)
  have e := evalW_eq_of_nfWM_eq hw hw' (h i hi j hj)
  rw [evalW_append, evalW_append, evalW_append] at e
  rw [qr, qr, e]
  congr 1
  split_ifs <;> simp [zb, evalW_singleton, xr_twenty, evalW_nil, *]

theorem qr_mul_self
    {i : ℕ} (hi : i < 15) : qr i * qr i = 1 := by
  have h := sqCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hw : ∀ k ∈ orbIdx i ++ orbIdx i, k < 21 := fun k hk => by
    rcases List.mem_append.1 hk with hk | hk <;> exact orbIdx_lt hi k hk
  rw [qr, ← evalW_append, evalW_eq_nfM _ hw, h i hi, nfM_zero]

theorem bC_fourteen_left {i : ℕ} (hi : i < 15) : bC 14 i = false := by
  have h := bC_fourteen
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact (h i hi).1

theorem bC_fourteen_right {i : ℕ} (hi : i < 15) : bC i 14 = false := by
  have h := bC_fourteen
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact (h i hi).2

theorem rels_qr :
    Rels qr rootInvM bC (List.range 15) where
  sq i hi := qr_mul_self (List.mem_range.1 hi)
  zsq := rootInvM_mul_self
  zcomm i hi := by
    have h := qr_mul_qr (by norm_num : 14 < 15) (List.mem_range.1 hi)
    rw [bC_fourteen_left (List.mem_range.1 hi), zb_false, mul_one, qr_fourteen] at h
    exact h
  rel i hi j hj := qr_mul_qr (List.mem_range.1 hi) (List.mem_range.1 hj)

end CFSG.Monster.B.E6.StdF4Radical
