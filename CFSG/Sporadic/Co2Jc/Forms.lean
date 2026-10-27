module

public import CFSG.Sporadic.Co2Jc.Linear
public import Certificates.Certificate719040

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem bit_testBit_xor (u w r : ℕ) :
    (if (u ^^^ w).testBit r then (1 : ZMod 2) else 0) =
      (if u.testBit r then (1 : ZMod 2) else 0) +
        (if w.testBit r then (1 : ZMod 2) else 0) := by
  rw [Nat.testBit_xor]
  cases hu : u.testBit r <;> cases hw : w.testBit r <;>
    simp [hu, hw, show (1 : ZMod 2) + 1 = 0 from by decide]

private theorem list_sum_map_range (n : ℕ) (f : ℕ → ZMod 2) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem bsum_foldr_list (n : ℕ) (c : ℕ → ℕ) (x : ℕ) (v : ℕ → ZMod 2) (l : List ℕ)
    (init : ℕ) :
    bsum n (l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) init) v =
      bsum n init v + (l.map fun i => if x.testBit i then bsum n (c i) v else 0).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    obtain h | h : x.testBit a = true ∨ x.testBit a = false := by cases x.testBit a <;> simp
    · rw [h]
      simp only [if_true]
      rw [bsum_xor, ih (init := init)]
      abel
    · rw [h]
      simp only [Bool.false_eq_true, if_false]
      rw [ih (init := init)]
      simp

private theorem bit_foldr_list (c : ℕ → ℕ) (x r : ℕ) (l : List ℕ) (init : ℕ) :
    (if (l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) init).testBit r
        then (1 : ZMod 2) else 0) =
      (if init.testBit r then (1 : ZMod 2) else 0) +
        (l.map fun i => if x.testBit i then
          (if (c i).testBit r then (1 : ZMod 2) else 0) else 0).sum := by
  induction l generalizing init with
  | nil =>
    rw [List.foldr_nil, List.map_nil, List.sum_nil, add_zero]
  | cons a l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    obtain h | h : x.testBit a = true ∨ x.testBit a = false := by cases x.testBit a <;> simp
    · rw [h]
      simp only [if_true]
      rw [bit_testBit_xor, ih (init := init)]
      abel
    · rw [h]
      simp only [Bool.false_eq_true, if_false]
      rw [ih (init := init)]
      simp

theorem bsum_colAct (n : ℕ) (c : ℕ → ℕ) (x : ℕ) (v : ℕ → ZMod 2) :
    bsum n (colAct c x) v = bsum 10 x fun i => bsum n (c i) v := by
  unfold colAct
  rw [bsum_foldr_list, bsum_zero, zero_add, list_sum_map_range]
  rfl

theorem testBit_colAct (c : ℕ → ℕ) (x r : ℕ) :
    (if (colAct c x).testBit r then (1 : ZMod 2) else 0) =
      bsum 10 x fun i => if (c i).testBit r then (1 : ZMod 2) else 0 := by
  unfold colAct
  rw [bit_foldr_list, list_sum_map_range]
  simp [bsum]

private theorem bsum_eq_zero_of (n m : ℕ) (v : ℕ → ZMod 2) (h : ∀ i < n, v i = 0) :
    bsum n m v = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hb
  · exact h i (Finset.mem_range.1 hi)
  · rfl

private theorem bsum_congr_of (n m : ℕ) {f g : ℕ → ZMod 2} (h : ∀ i < n, f i = g i) :
    bsum n m f = bsum n m g := by
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with hb
  · rw [h i (Finset.mem_range.1 hi)]
  · rfl

private theorem bsum_foldl_xor (n : ℕ) (E : Array ℕ) (v : ℕ → ZMod 2) (l : List ℕ) :
    ∀ init, bsum n (l.foldl (fun acc e => acc ^^^ E[e]!) init) v =
      bsum n init v + (l.map fun e => bsum n (E[e]!) v).sum := by
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih (init := init ^^^ E[a]!), bsum_xor, List.map_cons, List.sum_cons]
    abel

private theorem bsum_foldEqs (n : ℕ) (E : Array ℕ) (m : ℕ) (v : ℕ → ZMod 2)
    (h : ∀ a ∈ E, bsum n a v = 0) : bsum n (Native.foldEqs E m) v = 0 := by
  unfold Native.foldEqs
  rw [bsum_foldl_xor, bsum_zero, zero_add]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  have he' : e < E.size := List.mem_range.1 (List.mem_filter.1 he).1
  have hmem : E[e]! ∈ E := by
    rw [getElem!_pos (c := E) (i := e) he']
    exact Array.getElem_mem he'
  exact h _ hmem

private theorem glNJT_lt {k x : ℕ} (hk : k < 3) : Co2Smith.Native.glNJT k x < 1024 := by
  rw [glNJT_eq_colAct]
  refine colAct_lt ?_ x
  intro i hi
  interval_cases k <;> interval_cases i <;> decide

private theorem coord_qA {k : ℕ} (hk : k < 3) (w : ↥Jc) :
    coord (qA k w) = Co2Smith.Native.glNJT k (coord w) := by
  have h := qA_jcA hk (coord w)
  rw [jcA_coord] at h
  rw [h, coord_jcA (glNJT_lt hk)]

private theorem bilinCheck_spec (h : Native.bilinCheck = true) :
    ∀ u < 100, Native.foldEqs Native.bilinEqs (Data.bilinUnits[u]!) = 2 ^ u := by
  intro u hu
  rw [Native.bilinCheck, Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  rw [List.all_eq_true] at hall
  have hlen' : Data.bilinUnits.length = 100 := by simpa using hlen
  simpa [Nat.one_shiftLeft] using hall u (List.mem_range.2 hu)

private theorem wedgeCheck_spec (h : Native.wedgeCheck = true) :
    ∀ i j r, i < j → j < 10 → r < 10 →
      Native.foldEqs Native.wedEqs (Data.wedUnits[10 * (10 * i + j) + r]!) =
        2 ^ (10 * (10 * i + j) + r) := by
  intro i j r hij hj hr
  rw [Native.wedgeCheck, Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  rw [List.all_eq_true] at hall
  have hlen' : Data.wedUnits.length = 1000 := by simpa using hlen
  have hi : i < 10 := by omega
  have hj' := hall i (List.mem_range.2 hi)
  rw [List.all_eq_true] at hj'
  have hr' := hj' j (List.mem_range.2 hj)
  rw [if_pos hij, List.all_eq_true] at hr'
  simpa [Nat.one_shiftLeft] using hr' r (List.mem_range.2 hr)

private theorem mem_bilinEqs {m : ℕ} (hm : m ∈ Native.bilinEqsList) :
    ∃ k, (k = 0 ∨ k = 2) ∧ ∃ i < 10, ∃ j < 10, Native.bilinEq k i j = m := by
  simpa only [Native.bilinEqsList, List.mem_flatMap, List.mem_cons, List.mem_range,
    List.mem_map, List.not_mem_nil, or_false] using hm

private theorem mem_wedEqs {m : ℕ} (hm : m ∈ Native.wedEqsList) :
    ∃ k, (k = 0 ∨ k = 2) ∧ ∃ i < 10, ∃ j < 10, i < j ∧ ∃ r < 10,
      Native.wedEq k i j r = m := by
  simp only [Native.wedEqsList, List.mem_flatMap, List.mem_cons, List.mem_range,
    List.mem_map, List.not_mem_nil, or_false] at hm
  obtain ⟨k, hk, i, hi, j, hj, hm⟩ := hm
  refine ⟨k, hk, i, hi, j, hj, ?_, ?_⟩
  · by_contra h
    rw [if_neg h] at hm
    exact List.not_mem_nil hm
  · by_cases hij : i < j
    · rw [if_pos hij] at hm
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hm
      exact ⟨r, List.mem_range.1 hr, rfl⟩
    · rw [if_neg hij] at hm
      exact absurd hm List.not_mem_nil

private theorem bilinEqs_zero (β : ↥Jc → ↥Jc → ZMod 2)
    (h1 : ∀ a b c, β (a * b) c = β a c + β b c) (h2 : ∀ a b c, β a (b * c) = β a b + β a c)
    (hQ : ∀ g ∈ Qj, ∀ a b, β (g a) (g b) = β a b) (v : ℕ → ZMod 2)
    (hv : ∀ p q, p < 10 → q < 10 → v (10 * p + q) = β (jcA (2 ^ p)) (jcA (2 ^ q))) :
    ∀ m ∈ Native.bilinEqs, bsum 100 m v = 0 := by
  intro m hm
  have hm' : m ∈ Native.bilinEqsList := by
    have := (Array.mem_toList_iff (xs := Native.bilinEqs)).2 hm
    simpa [Native.bilinEqs] using this
  obtain ⟨k, hk, i, hi, j, hj, rfl⟩ := mem_bilinEqs hm'
  have hk3 : k < 3 := by rcases hk with rfl | rfl <;> norm_num
  have hpair : bsum 100 (Native.pairMask (Co2Smith.Native.glNJT k (2 ^ i))
      (Co2Smith.Native.glNJT k (2 ^ j))) v =
      bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          β (jcA (2 ^ p)) (jcA (2 ^ q)) := by
    rw [Native.pairMask, bsum_colAct]
    apply bsum_congr_of
    intro p hp
    rw [bsum_colAct]
    apply bsum_congr_of
    intro q hq
    rw [Native.uBilin, Nat.one_shiftLeft, bsum_two_pow (by omega)]
    exact hv p q hp hq
  have hbeta : β (jcA (Co2Smith.Native.glNJT k (2 ^ i)))
      (jcA (Co2Smith.Native.glNJT k (2 ^ j))) =
      bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          β (jcA (2 ^ p)) (jcA (2 ^ q)) := by
    have hadd : ∀ x y : ↥Jc, β (x * y) (jcA (Co2Smith.Native.glNJT k (2 ^ j))) =
        β x (jcA (Co2Smith.Native.glNJT k (2 ^ j))) +
          β y (jcA (Co2Smith.Native.glNJT k (2 ^ j))) := fun x y => h1 x y _
    have hstep := additive_jcA (f := fun z => β z (jcA (Co2Smith.Native.glNJT k (2 ^ j))))
      hadd (show Co2Smith.Native.glNJT k (2 ^ i) < 1024 from glNJT_lt hk3)
    change β (jcA (Co2Smith.Native.glNJT k (2 ^ i)))
      (jcA (Co2Smith.Native.glNJT k (2 ^ j))) = _
    rw [hstep]
    apply bsum_congr_of
    intro p hp
    exact additive_jcA (f := fun z => β (jcA (2 ^ p)) z)
      (fun x y => h2 (jcA (2 ^ p)) x y)
      (show Co2Smith.Native.glNJT k (2 ^ j) < 1024 from glNJT_lt hk3)
  have hlin : bsum 100 (Native.pairMask (Co2Smith.Native.glNJT k (2 ^ i))
      (Co2Smith.Native.glNJT k (2 ^ j))) v =
      β (qA k (jcA (2 ^ i))) (qA k (jcA (2 ^ j))) := by
    rw [hpair, qA_jcA hk3, qA_jcA hk3]
    exact hbeta.symm
  have hunit : bsum 100 (Native.uBilin i j) v = β (jcA (2 ^ i)) (jcA (2 ^ j)) := by
    rw [Native.uBilin, Nat.one_shiftLeft, bsum_two_pow (by omega)]
    exact hv i j hi hj
  rw [Native.bilinEq, bsum_xor, hlin, hunit, hQ (qA k) (qA_mem hk3) (jcA (2 ^ i)) (jcA (2 ^ j))]
  exact zmod2_add_self _

private theorem wedge_diag_bit {β : ↥Jc → ↥Jc → ↥Jc} (h3 : ∀ a, β a a = 1) (p r : ℕ) :
    (if (coord (β (jcA (2 ^ p)) (jcA (2 ^ p)))).testBit r then (1 : ZMod 2) else 0) = 0 := by
  rw [h3, coord_one]
  simp

private theorem bool_cases (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

private theorem wedge_symm {β : ↥Jc → ↥Jc → ↥Jc}
    (h1 : ∀ a b c, β (a * b) c = β a c * β b c)
    (h2 : ∀ a b c, β a (b * c) = β a b * β a c) (h3 : ∀ a, β a a = 1) (a b : ↥Jc) :
    β a b = β b a := by
  have hsq : ∀ x : ↥Jc, x * x = 1 := by
    intro x
    rw [← jcA_coord x, ← jcA_xor]
    simp [jcA_zero]
  have h := h3 (a * b)
  rw [h1 a b (a * b), h2 a a b, h2 b a b, h3 a, h3 b, one_mul, mul_one] at h
  have hba : β b a = β a b := by
    calc β b a = 1 * β b a := (one_mul _).symm
      _ = (β a b * β a b) * β b a := by rw [hsq]
      _ = β a b * (β a b * β b a) := by rw [mul_assoc]
      _ = β a b * 1 := by rw [h]
      _ = β a b := mul_one _
  exact hba.symm

private theorem wedge_bit_eq_bsum (β : ↥Jc → ↥Jc → ↥Jc)
    (h1 : ∀ a b c, β (a * b) c = β a c * β b c)
    (h2 : ∀ a b c, β a (b * c) = β a b * β a c)
    (r m n : ℕ) (hm : m < 1024) (hn : n < 1024) :
    (if (coord (β (jcA m) (jcA n))).testBit r then (1 : ZMod 2) else 0) =
      bsum 10 m fun p => bsum 10 n fun q =>
        if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit r then (1 : ZMod 2) else 0 := by
  have hf : ∀ x y : ↥Jc,
      (fun z => if (coord (β z (jcA n))).testBit r then (1 : ZMod 2) else 0) (x * y) =
        (fun z => if (coord (β z (jcA n))).testBit r then (1 : ZMod 2) else 0) x +
          (fun z => if (coord (β z (jcA n))).testBit r then (1 : ZMod 2) else 0) y := by
    intro x y
    change (if (coord (β (x * y) (jcA n))).testBit r then (1 : ZMod 2) else 0) =
      (if (coord (β x (jcA n))).testBit r then (1 : ZMod 2) else 0) +
        (if (coord (β y (jcA n))).testBit r then (1 : ZMod 2) else 0)
    rw [h1 x y (jcA n), coord_mul, bit_testBit_xor]
  have hg : ∀ p : ℕ, ∀ x y : ↥Jc,
      (fun z => if (coord (β (jcA (2 ^ p)) z)).testBit r then (1 : ZMod 2) else 0) (x * y) =
        (fun z => if (coord (β (jcA (2 ^ p)) z)).testBit r then (1 : ZMod 2) else 0) x +
          (fun z => if (coord (β (jcA (2 ^ p)) z)).testBit r then (1 : ZMod 2) else 0) y := by
    intro p x y
    change (if (coord (β (jcA (2 ^ p)) (x * y))).testBit r then (1 : ZMod 2) else 0) =
      (if (coord (β (jcA (2 ^ p)) x)).testBit r then (1 : ZMod 2) else 0) +
        (if (coord (β (jcA (2 ^ p)) y)).testBit r then (1 : ZMod 2) else 0)
    rw [h2 (jcA (2 ^ p)) x y, coord_mul, bit_testBit_xor]
  have hstep := additive_jcA
    (f := fun z => if (coord (β z (jcA n))).testBit r then (1 : ZMod 2) else 0) hf hm
  change (if (coord (β (jcA m) (jcA n))).testBit r then (1 : ZMod 2) else 0) = _
  rw [hstep]
  apply bsum_congr_of
  intro p hp
  exact additive_jcA (f := fun z =>
    if (coord (β (jcA (2 ^ p)) z)).testBit r then (1 : ZMod 2) else 0) (hg p) hn

private theorem wedge_rhs_bit (β : ↥Jc → ↥Jc → ↥Jc) {k i j r : ℕ} (hk : k < 3) :
    (if (coord (qA k (β (jcA (2 ^ i)) (jcA (2 ^ j))))).testBit r then (1 : ZMod 2) else 0) =
      bsum 10 (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))) fun s =>
        if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then (1 : ZMod 2) else 0 := by
  rw [coord_qA hk, glNJT_eq_colAct, testBit_colAct]
  refine Finset.sum_congr rfl fun s hs => ?_
  dsimp only
  rw [glNJT_eq_colAct, colAct_two_pow _ (Finset.mem_range.1 hs)]

private theorem wed_eq_zero (β : ↥Jc → ↥Jc → ↥Jc)
    (h1 : ∀ a b c, β (a * b) c = β a c * β b c) (h2 : ∀ a b c, β a (b * c) = β a b * β a c)
    (h3 : ∀ a, β a a = 1) (hQ : ∀ g ∈ Qj, ∀ a b, β (g a) (g b) = g (β a b))
    {k i j r : ℕ} (hk : k = 0 ∨ k = 2) (hi : i < 10) (hj : j < 10) (hij : i < j) (hr : r < 10)
    (v : ℕ → ZMod 2)
    (hv : ∀ p q s, p < q → q < 10 → s < 10 →
      v (10 * (10 * p + q) + s) =
        (if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit s then (1 : ZMod 2) else 0)) :
    bsum 1000 (Native.wedEq k i j r) v = 0 := by
  have hk3 : k < 3 := by rcases hk with rfl | rfl <;> norm_num
  have ha : Co2Smith.Native.glNJT k (2 ^ i) < 1024 := glNJT_lt hk3
  have hb : Co2Smith.Native.glNJT k (2 ^ j) < 1024 := glNJT_lt hk3
  have hL : bsum 1000 (Native.wedLhs k i j r) v =
      bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          if p = q then (0 : ZMod 2) else
            (if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit r then (1 : ZMod 2) else 0) := by
    rw [Native.wedLhs, bsum_colAct]
    apply bsum_congr_of
    intro p hp
    rw [bsum_colAct]
    apply bsum_congr_of
    intro q hq
    by_cases hpq : p = q
    · rw [hpq, if_pos rfl, bsum_zero, if_pos rfl]
    · rw [if_neg hpq, if_neg hpq, Native.uWedge]
      by_cases hlt : p < q
      · rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt),
          Nat.one_shiftLeft, bsum_two_pow (by omega)]
        exact hv p q r hlt (by omega) hr
      · rw [min_eq_right (le_of_lt (lt_of_le_of_ne (by omega) (Ne.symm hpq))),
          max_eq_left (le_of_lt (lt_of_le_of_ne (by omega) (Ne.symm hpq))),
          Nat.one_shiftLeft, bsum_two_pow (by omega)]
        rw [hv q p r (by omega) (by omega) hr,
          wedge_symm h1 h2 h3 (jcA (2 ^ p)) (jcA (2 ^ q))]
  have hL' : bsum 1000 (Native.wedLhs k i j r) v =
      bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit r then (1 : ZMod 2) else 0 := by
    rw [hL]
    apply bsum_congr_of
    intro p hp
    apply bsum_congr_of
    intro q hq
    by_cases hpq : p = q
    · rw [hpq, if_pos rfl, wedge_diag_bit h3 q r]
    · rw [if_neg hpq]
  have hR : bsum 1000 (Native.wedRhs k i j r) v =
      ((List.range 10).map fun s =>
        if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then
          (if (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))).testBit s then (1 : ZMod 2) else 0)
        else 0).sum := by
    rw [Native.wedRhs, bsum_xorList, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    have hs10 : s < 10 := List.mem_range.1 hs
    simp only [Function.comp_apply]
    obtain hg | hg := bool_cases ((Co2Smith.Native.glNJT k (2 ^ s)).testBit r)
    · rw [hg]
      simp only [if_true]
      change bsum 1000 (1 <<< (10 * (10 * i + j) + s)) v =
        (if (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))).testBit s then (1 : ZMod 2) else 0)
      rw [Nat.one_shiftLeft, bsum_two_pow (n := 1000) (by omega) v]
      exact hv i j s hij hj (List.mem_range.1 hs)
    · rw [hg]
      simp only [Bool.false_eq_true, if_false]
      change bsum 1000 0 v = 0
      rw [bsum_zero]
  have hLabs : (if (coord (β (qA k (jcA (2 ^ i))) (qA k (jcA (2 ^ j))))).testBit r
      then (1 : ZMod 2) else 0) =
      bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit r then (1 : ZMod 2) else 0 := by
    rw [qA_jcA hk3, qA_jcA hk3]
    exact wedge_bit_eq_bsum β h1 h2 r (Co2Smith.Native.glNJT k (2 ^ i))
      (Co2Smith.Native.glNJT k (2 ^ j)) ha hb
  have hRabs : (if (coord (qA k (β (jcA (2 ^ i)) (jcA (2 ^ j))))).testBit r
      then (1 : ZMod 2) else 0) =
      bsum 10 (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))) fun s =>
        if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then (1 : ZMod 2) else 0 :=
    wedge_rhs_bit β hk3
  have heq : bsum 10 (Co2Smith.Native.glNJT k (2 ^ i)) (fun p =>
        bsum 10 (Co2Smith.Native.glNJT k (2 ^ j)) fun q =>
          if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit r then (1 : ZMod 2) else 0) =
      bsum 10 (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))) fun s =>
        if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then (1 : ZMod 2) else 0 := by
    rw [← hLabs, ← hRabs, hQ (qA k) (qA_mem hk3) (jcA (2 ^ i)) (jcA (2 ^ j))]
  have hunit : bsum 1000 (Native.wedRhs k i j r) v =
      bsum 10 (coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))) fun s =>
        if (Co2Smith.Native.glNJT k (2 ^ s)).testBit r then (1 : ZMod 2) else 0 := by
    rw [hR]
    simp only [bsum]
    rw [← list_sum_map_range]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    obtain hw | hw := bool_cases ((coord (β (jcA (2 ^ i)) (jcA (2 ^ j)))).testBit s)
    · obtain hg | hg := bool_cases ((Co2Smith.Native.glNJT k (2 ^ s)).testBit r)
      · simp [hw, hg]
      · simp [hw, hg]
    · obtain hg | hg := bool_cases ((Co2Smith.Native.glNJT k (2 ^ s)).testBit r)
      · simp [hw, hg]
      · simp [hw, hg]
  rw [Native.wedEq, bsum_xor, hL', hunit, heq]
  exact zmod2_add_self _

theorem noBilin_Qj (β : ↥Jc → ↥Jc → ZMod 2) (h1 : ∀ a b c, β (a * b) c = β a c + β b c)
    (h2 : ∀ a b c, β a (b * c) = β a b + β a c) (hQ : ∀ g ∈ Qj, ∀ a b, β (g a) (g b) = β a b) :
    β = 0 := by
  funext a b
  let B : ℕ → ℕ → ZMod 2 := fun p q => β (jcA (2 ^ p)) (jcA (2 ^ q))
  let v : ℕ → ZMod 2 := fun u => B (u / 10) (u % 10)
  have hvB : ∀ p q, p < 10 → q < 10 → v (10 * p + q) = B p q := by
    intro p q hp hq
    simp only [v]
    rw [Nat.mul_add_div (by norm_num), Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
    simp [show q / 10 = 0 by omega]
  have hv : ∀ p q, p < 10 → q < 10 → v (10 * p + q) = β (jcA (2 ^ p)) (jcA (2 ^ q)) := by
    intro p q hp hq
    rw [hvB p q hp hq]
  have hparts : Native.bilinCheck = true ∧ Native.wedgeCheck = true := by
    rw [← Bool.and_eq_true]
    simpa [Native.formsOK] using (Certificates.certificate719040 : Native.formsOK = true)
  have hzero : ∀ m ∈ Native.bilinEqs, bsum 100 m v = 0 :=
    bilinEqs_zero β h1 h2 hQ v hv
  have hunit : ∀ u < 100, v u = 0 := by
    intro u hu
    have hspec : Native.foldEqs Native.bilinEqs (Data.bilinUnits[u]!) = 2 ^ u :=
      bilinCheck_spec hparts.1 u hu
    have hz : bsum 100 (Native.foldEqs Native.bilinEqs (Data.bilinUnits[u]!)) v = 0 :=
      bsum_foldEqs 100 Native.bilinEqs _ v hzero
    rw [hspec, bsum_two_pow hu v] at hz
    exact hz
  have hB : ∀ p q, p < 10 → q < 10 → B p q = 0 := by
    intro p q hp hq
    rw [← hvB p q hp hq]
    exact hunit (10 * p + q) (by omega)
  have hstep : β a b = bsum 10 (coord a) fun p => β (jcA (2 ^ p)) b := by
    have hadd : ∀ x y : ↥Jc, β (x * y) b = β x b + β y b := fun x y => h1 x y b
    have h := additive_jcA (f := fun z => β z b) hadd (coord_lt a)
    rwa [jcA_coord] at h
  rw [hstep]
  apply bsum_eq_zero_of
  intro p hp
  have hstep2 : β (jcA (2 ^ p)) b = bsum 10 (coord b) fun q => B p q := by
    have hadd : ∀ x y : ↥Jc, β (jcA (2 ^ p)) (x * y) =
        β (jcA (2 ^ p)) x + β (jcA (2 ^ p)) y := fun x y => h2 (jcA (2 ^ p)) x y
    have h := additive_jcA (f := fun z => β (jcA (2 ^ p)) z) hadd (coord_lt b)
    rwa [jcA_coord] at h
  rw [hstep2]
  exact bsum_eq_zero_of 10 (coord b) _ fun q hq => hB p q hp hq

theorem noWedge_Qj (β : ↥Jc → ↥Jc → ↥Jc) (h1 : ∀ a b c, β (a * b) c = β a c * β b c)
    (h2 : ∀ a b c, β a (b * c) = β a b * β a c) (h3 : ∀ a, β a a = 1)
    (hQ : ∀ g ∈ Qj, ∀ a b, β (g a) (g b) = g (β a b)) : ∀ a b, β a b = 1 := by
  let v : ℕ → ZMod 2 := fun u =>
    if (coord (β (jcA (2 ^ (u / 100))) (jcA (2 ^ ((u / 10) % 10))))).testBit (u % 10)
      then (1 : ZMod 2) else 0
  have hv : ∀ p q s, p < q → q < 10 → s < 10 →
      v (10 * (10 * p + q) + s) =
        (if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit s then (1 : ZMod 2) else 0) := by
    intro p q s hpq hq hs
    have hp : p < 10 := by omega
    simp only [v]
    have h1 : (10 * (10 * p + q) + s) / 100 = p := by
      rw [show 10 * (10 * p + q) + s = 100 * p + (10 * q + s) by ring]
      rw [Nat.mul_add_div (by norm_num), show (10 * q + s) / 100 = 0 by omega, Nat.add_zero]
    have h2 : (10 * (10 * p + q) + s) / 10 % 10 = q := by
      rw [show 10 * (10 * p + q) + s = 10 * (10 * p + q) + s by ring]
      rw [Nat.mul_add_div (by norm_num), show s / 10 = 0 by omega, Nat.add_zero,
        Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
    have h3 : (10 * (10 * p + q) + s) % 10 = s := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    rw [h1, h2, h3]
  have hparts : Native.bilinCheck = true ∧ Native.wedgeCheck = true := by
    rw [← Bool.and_eq_true]
    simpa [Native.formsOK] using (Certificates.certificate719040 : Native.formsOK = true)
  have hzero : ∀ m ∈ Native.wedEqs, bsum 1000 m v = 0 := by
    intro m hm
    have hm' : m ∈ Native.wedEqsList := by
      have := (Array.mem_toList_iff (xs := Native.wedEqs)).2 hm
      simpa [Native.wedEqs] using this
    obtain ⟨k, hk, i, hi, j, hj, hij, r, hr, rfl⟩ := mem_wedEqs hm'
    exact wed_eq_zero β h1 h2 h3 hQ hk hi hj hij hr v hv
  have hunit : ∀ i j r, i < j → j < 10 → r < 10 → v (10 * (10 * i + j) + r) = 0 := by
    intro i j r hij hj hr
    have hspec : Native.foldEqs Native.wedEqs (Data.wedUnits[10 * (10 * i + j) + r]!) =
        2 ^ (10 * (10 * i + j) + r) :=
      wedgeCheck_spec hparts.2 i j r hij hj hr
    have hz : bsum 1000 (Native.foldEqs Native.wedEqs
        (Data.wedUnits[10 * (10 * i + j) + r]!)) v = 0 :=
      bsum_foldEqs 1000 Native.wedEqs _ v hzero
    rw [hspec, bsum_two_pow (by omega) v] at hz
    exact hz
  have hall : ∀ p q s, p < 10 → q < 10 → s < 10 →
      (if (coord (β (jcA (2 ^ p)) (jcA (2 ^ q)))).testBit s then (1 : ZMod 2) else 0) = 0 := by
    intro p q s hp hq hs
    rcases lt_trichotomy p q with h | h | h
    · rw [← hv p q s h hq hs]
      exact hunit p q s h hq hs
    · subst h
      exact wedge_diag_bit h3 p s
    · rw [wedge_symm h1 h2 h3 (jcA (2 ^ p)) (jcA (2 ^ q)), ← hv q p s h hp hs]
      exact hunit q p s h hp hs
  intro a b
  have hbits : ∀ s, (coord (β a b)).testBit s = false := by
    intro s
    have hind : (if (coord (β a b)).testBit s then (1 : ZMod 2) else 0) = 0 := by
      by_cases hs : s < 10
      · have hb := wedge_bit_eq_bsum β h1 h2 s (coord a) (coord b) (coord_lt a) (coord_lt b)
        rw [jcA_coord, jcA_coord] at hb
        rw [hb]
        exact bsum_eq_zero_of 10 (coord a) _
          (fun p hp => bsum_eq_zero_of 10 (coord b) _ (fun q hq => hall p q s hp hq hs))
      · have hlt : (coord (β a b)).testBit s = false := by
          rw [Nat.testBit_eq_false_of_lt]
          have hc := coord_lt (β a b)
          have : 2 ^ 10 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        simp [hlt]
    obtain hh | hh := bool_cases ((coord (β a b)).testBit s)
    · rw [hh] at hind
      simp at hind
    · exact hh
  have hcoord : coord (β a b) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro s
    rw [hbits s]
    simp
  rw [← jcA_coord (β a b), hcoord, jcA_zero]

end CFSG.Sporadic.Co2Jc
