module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16M22K

@[expose] def insL (x : ℕ) (l : List ℕ) : List ℕ := if x ∈ l then l else x :: l

@[expose] def stepL (A B : ℕ → ℕ) (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => insL (A x) (insL (B x) acc)) l

@[expose] def goL (A B : ℕ → ℕ) : ℕ → List ℕ → List ℕ
  | 0, S => S
  | n + 1, S =>
      let S' := stepL A B S
      if S'.length = S.length then S' else goL A B n S'

@[expose] def spanL (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x)) [0]

@[expose] def maskL (l : List ℕ) : ℕ := l.foldl (fun m x => m ||| (1 <<< x)) 0

theorem foldl_or (l : List ℕ) (a : ℕ) :
    l.foldl (fun m x => m ||| (1 <<< x)) a = a ||| maskL l := by
  induction l generalizing a with
  | nil => simp [maskL]
  | cons x l ih =>
    simp only [List.foldl_cons, maskL]
    rw [ih, ih (0 ||| 1 <<< x), Nat.zero_or, Nat.or_assoc]

theorem maskL_cons (x : ℕ) (l : List ℕ) : maskL (x :: l) = (1 <<< x) ||| maskL l := by
  rw [maskL, List.foldl_cons, foldl_or, Nat.zero_or]

theorem maskL_append (l₁ l₂ : List ℕ) : maskL (l₁ ++ l₂) = maskL l₁ ||| maskL l₂ := by
  rw [maskL, List.foldl_append, foldl_or]
  rfl

theorem testBit_maskL (l : List ℕ) (y : ℕ) : (maskL l).testBit y = decide (y ∈ l) := by
  induction l with
  | nil => simp [maskL]
  | cons x l ih =>
    rw [maskL_cons, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : x = y
    · subst h
      simp
    · simp [h, Ne.symm h]

@[expose] noncomputable def forceN {α : Type} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem forceN_apply {α : Type} (y : ℕ) (k : ℕ → α) : forceN y k = k y := by
  cases y <;> rfl

@[expose] def bitK (m x : ℕ) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 x))

theorem bitK_eq (m x : ℕ) : bitK m x = m.testBit x := by
  have h : Nat.land m (Nat.shiftLeft 1 x) = if m.testBit x then 2 ^ x else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (m &&& (1 <<< x)).testBit i = _
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hb : m.testBit x
    · rw [if_pos hb, Nat.testBit_two_pow]
      by_cases hi : x = i
      · subst hi
        simp [hb]
      · simp [hi]
    · rw [if_neg hb, Nat.zero_testBit]
      by_cases hi : x = i
      · subst hi
        simp [hb]
      · simp [hi]
  unfold bitK
  rw [h]
  by_cases hb : m.testBit x
  · rw [if_pos hb, hb]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos x)
  · have hf : m.testBit x = false := by simpa using hb
    rw [if_neg hb, hf]
    rfl

@[expose] noncomputable def insC {α : Type} (y : ℕ) (l : List ℕ) (m c : ℕ)
    (k : List ℕ → ℕ → ℕ → α) : α :=
  forceN y fun y => Bool.rec (motive := fun _ => α)
    (forceN (Nat.lor (Nat.shiftLeft 1 y) m) fun m' => forceN (Nat.succ c) fun c' => k (y :: l) m' c')
    (k l m c) (bitK m y)

theorem insC_eq {α : Type} (y : ℕ) (l : List ℕ) (k : List ℕ → ℕ → ℕ → α) :
    insC y l (maskL l) l.length k = k (insL y l) (maskL (insL y l)) (insL y l).length := by
  unfold insC
  rw [forceN_apply, bitK_eq, testBit_maskL]
  by_cases h : y ∈ l
  · simp only [h, decide_true, insL, if_true]
  · simp only [h, decide_false, insL, if_false, forceN_apply, maskL_cons, List.length_cons]
    rfl

@[expose] noncomputable def foldC {α : Type} (A B : ℕ → ℕ) (xs : List ℕ) :
    (List ℕ → ℕ → ℕ → α) → List ℕ → ℕ → ℕ → α :=
  List.rec (motive := fun _ => (List ℕ → ℕ → ℕ → α) → List ℕ → ℕ → ℕ → α)
    (fun k l m c => k l m c)
    (fun x _ ih k l m c =>
      insC (B x) l m c fun l m c => insC (A x) l m c fun l m c => ih k l m c) xs

theorem foldC_eq {α : Type} (A B : ℕ → ℕ) (k : List ℕ → ℕ → ℕ → α) (xs l : List ℕ) :
    foldC A B xs k l (maskL l) l.length =
      k (xs.foldl (fun acc x => insL (A x) (insL (B x) acc)) l)
        (maskL (xs.foldl (fun acc x => insL (A x) (insL (B x) acc)) l))
        (xs.foldl (fun acc x => insL (A x) (insL (B x) acc)) l).length := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih =>
    change insC (B x) l (maskL l) l.length (fun l m c => insC (A x) l m c fun l m c =>
      foldC A B xs k l m c) = _
    rw [insC_eq, insC_eq, ih]
    rfl

@[expose] noncomputable def goC {α : Type} (A B : ℕ → ℕ) (n : ℕ) :
    (List ℕ → ℕ → ℕ → α) → List ℕ → ℕ → ℕ → α :=
  Nat.rec (motive := fun _ => (List ℕ → ℕ → ℕ → α) → List ℕ → ℕ → ℕ → α)
    (fun k l m c => k l m c)
    (fun _ ih k l m c => foldC A B l (fun l' m' c' =>
      Bool.rec (motive := fun _ => α) (ih k l' m' c') (k l' m' c') (Nat.beq c' c)) l m c) n

theorem goC_eq {α : Type} (A B : ℕ → ℕ) (k : List ℕ → ℕ → ℕ → α) (n : ℕ) (S : List ℕ) :
    goC A B n k S (maskL S) S.length = k (goL A B n S) (maskL (goL A B n S)) (goL A B n S).length := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    change foldC A B S (fun l' m' c' => Bool.rec (motive := fun _ => α) (goC A B n k l' m' c')
      (k l' m' c') (Nat.beq c' S.length)) S (maskL S) S.length = _
    rw [foldC_eq]
    simp only [goL]
    change Bool.rec (motive := fun _ => α) (goC A B n k (stepL A B S) (maskL (stepL A B S))
      (stepL A B S).length) _ (Nat.beq (stepL A B S).length S.length) = _
    cases hb : Nat.beq (stepL A B S).length S.length
    · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
      exact ih _
    · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
      rfl

@[expose] noncomputable def mapC {α : Type} (x : ℕ) (acc : List ℕ) : (List ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => (List ℕ → ℕ → α) → α) (fun k => k [] 0)
    (fun y _ ih k => ih fun l mm => forceN (Nat.xor y x) fun z =>
      forceN (Nat.lor (Nat.shiftLeft 1 z) mm) fun mm' => k (z :: l) mm') acc

theorem mapC_eq {α : Type} (x : ℕ) (acc : List ℕ) (k : List ℕ → ℕ → α) :
    mapC x acc k = k (acc.map (fun y => y ^^^ x)) (maskL (acc.map (fun y => y ^^^ x))) := by
  induction acc generalizing k with
  | nil => rfl
  | cons y acc ih =>
    change mapC x acc (fun l mm => forceN (Nat.xor y x) fun z =>
      forceN (Nat.lor (Nat.shiftLeft 1 z) mm) fun mm' => k (z :: l) mm') = _
    rw [ih, forceN_apply, forceN_apply, List.map_cons, maskL_cons]
    rfl

@[expose] noncomputable def spanC {α : Type} (xs : List ℕ) :
    (List ℕ → ℕ → α) → List ℕ → ℕ → α :=
  List.rec (motive := fun _ => (List ℕ → ℕ → α) → List ℕ → ℕ → α) (fun k acc m => k acc m)
    (fun x _ ih k acc m => Bool.rec (motive := fun _ => α)
      (mapC x acc fun l mm => forceN (Nat.lor m mm) fun m' => ih k (acc ++ l) m')
      (ih k acc m) (bitK m x)) xs

theorem spanC_eq' {α : Type} (k : List ℕ → ℕ → α) (xs acc : List ℕ) :
    spanC xs k acc (maskL acc) =
      k (xs.foldl (fun acc x => if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x)) acc)
        (maskL (xs.foldl
          (fun acc x => if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x)) acc)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => α)
      (mapC x acc fun l mm => forceN (Nat.lor (maskL acc) mm) fun m' => spanC xs k (acc ++ l) m')
      (spanC xs k acc (maskL acc)) (bitK (maskL acc) x) = _
    rw [bitK_eq, testBit_maskL, List.foldl_cons]
    by_cases h : x ∈ acc
    · simp only [h, decide_true, if_true]
      exact ih acc
    · simp only [h, decide_false, if_false]
      rw [mapC_eq, forceN_apply, ← ih (acc ++ acc.map (fun y => y ^^^ x)), maskL_append]
      rfl

theorem spanC_eq {α : Type} (k : List ℕ → ℕ → α) (xs : List ℕ) :
    spanC xs k [0] (maskL [0]) = k (spanL xs) (maskL (spanL xs)) :=
  spanC_eq' k xs [0]

@[expose] noncomputable def chkK (A B : ℕ → ℕ) (v₁ v₃ v₄ F : ℕ) : Bool :=
  goC A B 1200 (fun l₁ m₁ _ => goC A B 1200 (fun l₃ m₃ _ => goC A B 1200 (fun l₄ m₄ _ =>
    spanC l₁ (fun _ s₁ => spanC l₃ (fun _ s₃ => spanC l₄ (fun _ s₄ =>
      (((m₁ ||| m₃ ||| m₄) ||| 1) == F) && (s₁ == F) && (s₃ == F) && (s₄ == F))
      [0] (maskL [0])) [0] (maskL [0])) [0] (maskL [0]))
    [v₄] (maskL [v₄]) [v₄].length) [v₃] (maskL [v₃]) [v₃].length) [v₁] (maskL [v₁]) [v₁].length

theorem chkK_eq (A B : ℕ → ℕ) (v₁ v₃ v₄ F : ℕ) :
    chkK A B v₁ v₃ v₄ F =
      ((((maskL (goL A B 1200 [v₁]) ||| maskL (goL A B 1200 [v₃]) |||
        maskL (goL A B 1200 [v₄])) ||| 1) == F) &&
        (maskL (spanL (goL A B 1200 [v₁])) == F) &&
        (maskL (spanL (goL A B 1200 [v₃])) == F) &&
        (maskL (spanL (goL A B 1200 [v₄])) == F)) := by
  unfold chkK
  simp only [goC_eq, spanC_eq]

@[expose] def xorK (a c v j : ℕ) : ℕ := Nat.xor a (Nat.mul c (Nat.land (Nat.shiftRight v j) 1))

theorem xorK_eq (a c v j : ℕ) : (if v.testBit j then a ^^^ c else a) = xorK a c v j := by
  have hb : Nat.land (Nat.shiftRight v j) 1 = if v.testBit j then 1 else 0 := by
    change (v >>> j) &&& 1 = _
    have h1 : v.testBit j = (v >>> j).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
    rw [h1, Nat.testBit_zero, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one (v >>> j) with h | h <;> simp [h]
  unfold xorK
  rw [hb]
  by_cases h : v.testBit j
  · rw [if_pos h, if_pos h]
    change a ^^^ c = a ^^^ (c * 1)
    rw [Nat.mul_one]
  · rw [if_neg h, if_neg h]
    change a = a ^^^ (c * 0)
    rw [Nat.mul_zero, Nat.xor_zero]

@[expose] def appK (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ v : ℕ) : ℕ :=
  xorK (xorK (xorK (xorK (xorK (xorK (xorK (xorK (xorK (xorK 0 c₀ v 0) c₁ v 1) c₂ v 2) c₃ v 3)
    c₄ v 4) c₅ v 5) c₆ v 6) c₇ v 7) c₈ v 8) c₉ v 9

theorem app_eq (c : ℕ → ℕ) (v : ℕ) :
    (List.range 10).foldl (fun acc j => if v.testBit j then acc ^^^ c j else acc) 0 =
      appK (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) v := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil, xorK_eq, appK]

theorem dec_fold {V : Type*} [AddCommMonoid V] (dec : ℕ → V) (h0 : dec 0 = 0)
    (hx : ∀ x y, dec (x ^^^ y) = dec x + dec y) (v : ℕ) (c : ℕ → ℕ) (l : List ℕ) :
    dec (l.foldl (fun acc j => if v.testBit j then acc ^^^ c j else acc) 0) =
      (l.map fun j => if v.testBit j then dec (c j) else 0).sum := by
  have key : ∀ (l : List ℕ) (a : ℕ),
      dec (l.foldl (fun acc j => if v.testBit j then acc ^^^ c j else acc) a) =
        dec a + (l.map fun j => if v.testBit j then dec (c j) else 0).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons j l ih =>
      intro a
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
      by_cases h : v.testBit j
      · rw [if_pos h, if_pos h, hx]
      · rw [if_neg h, if_neg h, add_zero]
  rw [key, h0, zero_add]

theorem sum_range_fin {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j : Fin n, f j := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16M22K

end
