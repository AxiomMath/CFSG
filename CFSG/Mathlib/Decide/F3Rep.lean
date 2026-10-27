module

public import CFSG.F3.Spec

public section

namespace CFSG.Decide.F3

open CFSG.F3.Native

@[expose] def allVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun l => [0 :: l, 1 :: l, 2 :: l]

@[expose] def repVecs : ℕ → List (List ℕ)
  | 0 => []
  | n + 1 => (allVecs n).map (1 :: ·) ++ (repVecs n).map (0 :: ·)

@[expose] def vecOfList (d : ℕ) (l : List ℕ) : Fin d → ZMod 3 := fun k => (l.getD k 0 : ZMod 3)

theorem mem_allVecs {d : ℕ} {l : List ℕ} : l ∈ allVecs d ↔ l.length = d ∧ ∀ a ∈ l, a < 3 := by
  induction d generalizing l with
  | zero =>
    simp [allVecs]
    rintro rfl
    simp
  | succ n ih =>
    rw [allVecs, List.mem_flatMap]
    constructor
    · rintro ⟨l', hl', hl⟩
      rw [ih] at hl'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;>
        exact ⟨by simp [hl'], by
          intro a ha
          rw [List.mem_cons] at ha
          rcases ha with rfl | ha
          · norm_num
          · exact hl'.2 a ha⟩
    · rintro ⟨hlen, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        have ha : a < 3 := hlt a (by simp)
        have hl' : l'.length = n := by simpa using hlen
        have hlt' : ∀ b ∈ l', b < 3 := fun b hb => hlt b (by simp [hb])
        have hmem : l' ∈ allVecs n := ih.2 ⟨hl', hlt'⟩
        interval_cases a <;> exact ⟨l', hmem, by simp⟩

private theorem listOfFn_val_mem (n : ℕ) (g : Fin n → ZMod 3) :
    (List.ofFn fun k : Fin n => (g k).val) ∈ allVecs n := by
  rw [mem_allVecs]
  refine ⟨List.length_ofFn, ?_⟩
  intro a ha
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
  exact ZMod.val_lt (g k)

private theorem exists_repVecs_head_one {n : ℕ} {v : Fin (n + 1) → ZMod 3} (h1 : v 0 = 1) :
    ∃ l ∈ repVecs (n + 1), vecOfList (n + 1) l = v := by
  refine ⟨1 :: List.ofFn (fun k : Fin n => (v k.succ).val), ?_, ?_⟩
  · rw [repVecs]
    exact List.mem_append.2 (Or.inl (List.mem_map.2
      ⟨_, listOfFn_val_mem n (Fin.tail v), rfl⟩))
  · funext k
    refine Fin.cases ?_ ?_ k
    · simp [vecOfList, h1]
    · intro j
      have hval : ((v j.succ).val : ZMod 3) = v j.succ := ZMod.natCast_zmod_val _
      simpa [vecOfList] using hval

private theorem exists_repVecs_head_two {n : ℕ} {v : Fin (n + 1) → ZMod 3} (h2 : v 0 = 2) :
    ∃ l ∈ repVecs (n + 1), vecOfList (n + 1) l = 2 • v := by
  refine ⟨1 :: List.ofFn (fun k : Fin n => ((2 : ZMod 3) * v k.succ).val), ?_, ?_⟩
  · rw [repVecs]
    exact List.mem_append.2 (Or.inl (List.mem_map.2
      ⟨_, listOfFn_val_mem n (fun k : Fin n => (2 : ZMod 3) * v k.succ), rfl⟩))
  · funext k
    refine Fin.cases ?_ ?_ k
    · have hval : (2 : ZMod 3) • v 0 = 1 := by rw [h2]; decide
      simpa [vecOfList] using hval.symm
    · intro j
      have hval : (((2 : ZMod 3) * v j.succ).val : ZMod 3) = (2 : ZMod 3) * v j.succ :=
        ZMod.natCast_zmod_val _
      simpa [vecOfList] using hval

theorem exists_mem_repVecs {d : ℕ} {v : Fin d → ZMod 3} (hv : v ≠ 0) :
    ∃ l ∈ repVecs d, vecOfList d l = v ∨ vecOfList d l = 2 • v := by
  induction d with
  | zero => exact absurd (Subsingleton.elim v 0) hv
  | succ n ih =>
    have hv0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by
      have h : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      exact h (v 0)
    rcases hv0 with h0 | h1 | h2
    · have htail : Fin.tail v ≠ 0 := by
        intro h
        apply hv
        funext k
        exact Fin.cases h0 (fun j => congrFun h j) k
      obtain ⟨l, hl, hvl⟩ := ih htail
      refine ⟨0 :: l, ?_, ?_⟩
      · rw [repVecs]
        exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨l, hl, rfl⟩))
      · rcases hvl with hvl | hvl
        · left
          funext k
          refine Fin.cases ?_ ?_ k
          · simp [vecOfList, h0]
          · intro j
            have h1 : vecOfList (n + 1) (0 :: l) j.succ = vecOfList n l j := by
              simp [vecOfList]
            rw [h1, hvl]
            rfl
        · right
          funext k
          refine Fin.cases ?_ ?_ k
          · simp [vecOfList, h0]
          · intro j
            have h1 : vecOfList (n + 1) (0 :: l) j.succ = vecOfList n l j := by
              simp [vecOfList]
            rw [h1, hvl]
            rfl
    · obtain ⟨l, hl, hvl⟩ := exists_repVecs_head_one h1
      exact ⟨l, hl, Or.inl hvl⟩
    · obtain ⟨l, hl, hvl⟩ := exists_repVecs_head_two h2
      exact ⟨l, hl, Or.inr hvl⟩

@[expose] def ofFnS (f : ℕ → ℕ) : ℕ → V
  | 0 => V.zero
  | j + 1 => ofFnStep f j (ofFnS f j)

theorem ofFnS_eq (f : ℕ → ℕ) (d : ℕ) : ofFnS f d = V.ofFn d f := by
  induction d with
  | zero => rw [ofFn_eq_fold, Nat.fold_zero]; rfl
  | succ n ih =>
    change ofFnStep f n (ofFnS f n) = V.ofFn (n + 1) f
    rw [ofFn_eq_fold, Nat.fold_succ, ih, ofFn_eq_fold]

@[expose] def combS (Y : Array V) (r : V) : ℕ → V
  | 0 => V.zero
  | j + 1 => combStep Y r j (combS Y r j)

theorem combS_eq (Y : Array V) (r : V) (d : ℕ) : combS Y r d = comb d Y r := by
  induction d with
  | zero => rw [comb_eq_fold, Nat.fold_zero]; rfl
  | succ n ih =>
    change combStep Y r n (combS Y r n) = comb (n + 1) Y r
    rw [comb_eq_fold, Nat.fold_succ, ih, comb_eq_fold]

@[expose] def zeroMask (N : ℕ) (x : V) : ℕ := (2 ^ N - 1) ^^^ ((2 ^ N - 1) &&& (x.p ||| x.m))

theorem testBit_zeroMask {N i : ℕ} (hi : i < N) (x : V) :
    (zeroMask N x).testBit i = true ↔ x.val i = 0 := by
  rw [zeroMask, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, V.val_eq_bitVal]
  simp only [hi, decide_true, Bool.true_and]
  cases hp : x.p.testBit i <;> cases hm : x.m.testBit i <;>
    simp [bitVal, hp, hm] <;> decide

theorem testBit_zeroMask_of_le {N i : ℕ} (hi : N ≤ i) (x : V) :
    (zeroMask N x).testBit i = false := by
  rw [zeroMask, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one]
  have h : (decide (i < N)) = false := decide_eq_false (Nat.not_lt.mpr hi)
  rw [h]
  simp

@[expose] def maskOf : List ℕ → ℕ
  | [] => 0
  | i :: l => 2 ^ i ||| maskOf l

theorem testBit_maskOf (l : List ℕ) (i : ℕ) : (maskOf l).testBit i = true ↔ i ∈ l := by
  induction l with
  | nil => simp [maskOf]
  | cons a l ih =>
    rw [maskOf, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    rw [ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

end CFSG.Decide.F3
