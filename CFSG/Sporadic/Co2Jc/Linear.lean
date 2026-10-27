module

public import CFSG.Sporadic.Co2Jc.Bits
public import CFSG.Sporadic.Co2Jc.Model

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith

theorem two_pow_lt_1024 {i : ℕ} (hi : i < 10) : 2 ^ i < 1024 := by
  calc 2 ^ i < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hi
    _ = 1024 := by norm_num

private theorem jcA_eq_jcFold (x : ℕ) :
    jcA x = (⟨jcFold x (List.range 10),
      jcFold_mem x (List.range 10) (fun _ hi => List.mem_range.1 hi)⟩ : ↥Jc) := by
  apply Subtype.ext
  rw [coe_jcA]
  exact jcElt_eq_jcFold x

private theorem map_jcFold (f : ↥Jc →* ↥Jc) (c : ℕ → ℕ)
    (hc : ∀ i < 10, f (jcA (2 ^ i)) = jcA (c i)) :
    ∀ (l : List ℕ) (hl : ∀ i ∈ l, i < 10) (x : ℕ),
      f (⟨jcFold x l, jcFold_mem x l hl⟩ : ↥Jc) =
        jcA (l.foldr (fun i acc => if x.testBit i then c i ^^^ acc else acc) 0)
  | [], _, x => by
    have h1 : (⟨jcFold x [], jcFold_mem x [] (by simp)⟩ : ↥Jc) = 1 := Subtype.ext rfl
    rw [h1, map_one]
    exact (jcA_zero).symm
  | i :: l, hl, x => by
    have hi : i < 10 := hl i (by simp)
    have hl' : ∀ j ∈ l, j < 10 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hP : (⟨jcFold x (i :: l), jcFold_mem x (i :: l) hl⟩ : ↥Jc) =
        (if x.testBit i then jcA (2 ^ i) * ⟨jcFold x l, jcFold_mem x l hl'⟩
         else ⟨jcFold x l, jcFold_mem x l hl'⟩) := by
      by_cases hbit : x.testBit i
      · rw [if_pos hbit]
        apply Subtype.ext
        change jcFold x (i :: l) = (jcA (2 ^ i) : K) * jcFold x l
        rw [coe_jcA, jcElt_two_pow hi]
        rw [show jcFold x (i :: l) =
          (if x.testBit i then jcB i * jcFold x l else jcFold x l) from rfl, if_pos hbit]
      · rw [if_neg hbit]
        apply Subtype.ext
        change jcFold x (i :: l) = jcFold x l
        rw [show jcFold x (i :: l) =
          (if x.testBit i then jcB i * jcFold x l else jcFold x l) from rfl, if_neg hbit]
    rw [hP]
    by_cases hbit : x.testBit i
    · rw [if_pos hbit, map_mul, hc i hi, map_jcFold f c hc l hl' x, ← jcA_xor,
        List.foldr_cons, if_pos hbit]
    · rw [if_neg hbit, map_jcFold f c hc l hl' x, List.foldr_cons, if_neg hbit]

theorem hom_jcA_of_basis {f : ↥Jc →* ↥Jc} {c : ℕ → ℕ} (h : ∀ i < 10, f (jcA (2 ^ i)) = jcA (c i))
    {x : ℕ} (hx : x < 1024) : f (jcA x) = jcA (colAct c x) := by
  rw [jcA_eq_jcFold x]
  simpa [colAct] using map_jcFold f c h (List.range 10)
    (fun _ hi => List.mem_range.1 hi) x

private theorem map_jcFold_add (f : ↥Jc → ZMod 2)
    (hf : ∀ a b, f (a * b) = f a + f b) :
    ∀ (l : List ℕ) (hl : ∀ i ∈ l, i < 10) (x : ℕ),
      f (⟨jcFold x l, jcFold_mem x l hl⟩ : ↥Jc) =
        l.foldr (fun i acc => if x.testBit i then f (jcA (2 ^ i)) + acc else acc) 0
  | [], _, x => by
    have h1 : (⟨jcFold x [], jcFold_mem x [] (by simp)⟩ : ↥Jc) = 1 := Subtype.ext rfl
    have hf1 : f 1 = 0 := by
      have h := hf 1 1
      simp only [mul_one] at h
      have h' : f 1 + 0 = f 1 + f 1 := by
        rw [add_zero]
        exact h
      exact (add_left_cancel h').symm
    rw [h1, hf1]
    rfl
  | i :: l, hl, x => by
    have hi : i < 10 := hl i (by simp)
    have hl' : ∀ j ∈ l, j < 10 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hP : (⟨jcFold x (i :: l), jcFold_mem x (i :: l) hl⟩ : ↥Jc) =
        (if x.testBit i then jcA (2 ^ i) * ⟨jcFold x l, jcFold_mem x l hl'⟩
         else ⟨jcFold x l, jcFold_mem x l hl'⟩) := by
      by_cases hbit : x.testBit i
      · rw [if_pos hbit]
        apply Subtype.ext
        change jcFold x (i :: l) = (jcA (2 ^ i) : K) * jcFold x l
        rw [coe_jcA, jcElt_two_pow hi]
        rw [show jcFold x (i :: l) =
          (if x.testBit i then jcB i * jcFold x l else jcFold x l) from rfl, if_pos hbit]
      · rw [if_neg hbit]
        apply Subtype.ext
        change jcFold x (i :: l) = jcFold x l
        rw [show jcFold x (i :: l) =
          (if x.testBit i then jcB i * jcFold x l else jcFold x l) from rfl, if_neg hbit]
    rw [hP]
    by_cases hbit : x.testBit i
    · rw [if_pos hbit, hf, map_jcFold_add f hf l hl' x, List.foldr_cons, if_pos hbit]
    · rw [if_neg hbit, map_jcFold_add f hf l hl' x, List.foldr_cons, if_neg hbit]

private theorem foldr_range_add (n x : ℕ) (v : ℕ → ZMod 2) (a : ZMod 2) :
    (List.range n).foldr (fun i acc => if x.testBit i then v i + acc else acc) a =
      (∑ i ∈ Finset.range n, if x.testBit i then v i else 0) + a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih, Finset.sum_range_succ]
    by_cases h : x.testBit n
    · simp [h, add_assoc]
    · simp [h]

theorem additive_jcA {f : ↥Jc → ZMod 2} (hf : ∀ a b, f (a * b) = f a + f b) {x : ℕ}
    (hx : x < 1024) : f (jcA x) = bsum 10 x fun i => f (jcA (2 ^ i)) := by
  rw [jcA_eq_jcFold x, map_jcFold_add f hf (List.range 10)
    (fun _ hi => List.mem_range.1 hi) x, foldr_range_add]
  simp [bsum]

theorem additive_eq_zero {f : ↥Jc → ZMod 2} (hf : ∀ a b, f (a * b) = f a + f b)
    (h : ∀ i < 10, f (jcA (2 ^ i)) = 0) (a : ↥Jc) : f a = 0 := by
  obtain ⟨m, hm, rfl⟩ := exists_jcA a
  rw [additive_jcA hf hm, bsum]
  exact Finset.sum_eq_zero fun i hi => by
    rw [h i (Finset.mem_range.1 hi)]
    simp

theorem qWord_jcA_eq_colAct {w : List ℕ} (hw : ∀ k ∈ w, k < 3) {x : ℕ} (hx : x < 1024) :
    qWord w (jcA x) = jcA (colAct (fun i => wordAct w (2 ^ i)) x) :=
  hom_jcA_of_basis (f := qWord w) (c := fun i => wordAct w (2 ^ i))
    (fun i _ => qWord_jcA hw (2 ^ i)) hx

end CFSG.Sporadic.Co2Jc
