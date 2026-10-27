module

public import CFSG.RankThree.GF2n.Parrott.SpinXChecks

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinRigid.HbadTPack

open CFSG.RankThree.GF2n.Parrott.SpinRigid

@[expose] noncomputable def selB (b c : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ _ => c) b

@[expose] noncomputable def bitK (m i : Nat) : Nat := Nat.land (Nat.shiftRight m i) 1

@[expose] noncomputable def bapK (A : B8) (m : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (selB (bitK m 0) A.c0) (selB (bitK m 1) A.c1)) (selB (bitK m 2) A.c2))
    (selB (bitK m 3) A.c3)) (selB (bitK m 4) A.c4)) (selB (bitK m 5) A.c5))
    (selB (bitK m 6) A.c6)) (selB (bitK m 7) A.c7)

theorem ite_bit (m i c : Nat) : (if m.testBit i then c else 0) = selB (bitK m i) c := by
  have h : bitK m i = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with e | e <;> rw [e] <;> rfl

theorem bapply_eq (A : B8) (m : Nat) : bapply A m = bapK A m := by
  unfold bapply bapK
  simp only [ite_bit]
  rfl

@[expose] def qMask : Nat :=
  1651976815820641022012551806831831218800443692206288542932271324739048689514

@[expose] noncomputable def bqK (m n : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (bitK qMask (Nat.xor m n)) (bitK qMask m)) (bitK qMask n)) 2

theorem qTab_lt : ∀ x < 256, qTab.getD x 0 = bitK qMask x := by decide +kernel

theorem qTab_getD (x : Nat) : qTab.getD x 0 = bitK qMask x := by
  rcases Nat.lt_or_ge x 256 with hx | hx
  · exact qTab_lt x hx
  · have hl : qTab.length = 256 := by decide +kernel
    have hq : qMask < 2 ^ 256 := by decide +kernel
    have h0 : qMask / 2 ^ x = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) hx))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl]; exact hx)]
    change 0 = (qMask >>> x) &&& 1
    rw [Nat.shiftRight_eq_div_pow, h0]
    rfl

theorem bq_eq (m n : Nat) : bq m n = bqK m n := by
  unfold bq bqK
  rw [qTab_getD, qTab_getD, qTab_getD]
  rfl

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ r => Bool.rec (motive := fun _ => Bool) r true (Nat.beq x a)) L

@[expose] noncomputable def allK (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a _ r => Bool.rec (motive := fun _ => Bool) false r (f a)) L

theorem memK_eq (x : Nat) (L : List Nat) : decide (x ∈ L) = memK x L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change decide (x ∈ a :: L) = Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq x a)
    cases hb : Nat.beq x a
    · have hne : x ≠ a := Nat.ne_of_beq_eq_false hb
      rw [← ih]
      simp [hne]
    · have he : x = a := Nat.eq_of_beq_eq_true hb
      simp [he]

theorem all_eq (f : Nat → Bool) (L : List Nat) : L.all f = allK f L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.all_cons, ih]
    change (f a && allK f L) = Bool.rec (motive := fun _ => Bool) false (allK f L) (f a)
    cases f a <;> rfl

@[expose] def fixedL : List Nat :=
  [0, 4, 10, 14, 16, 20, 26, 30, 33, 37, 43, 47, 49, 53, 59, 63, 64, 68, 74, 78, 80, 84, 90, 94,
    97, 101, 107, 111, 113, 117, 123, 127, 128, 132, 138, 142, 144, 148, 154, 158, 161, 165, 171,
    175, 177, 181, 187, 191, 192, 196, 202, 206, 208, 212, 218, 222, 225, 229, 235, 239, 241, 245,
    251, 255]

theorem fixedL_eq : (List.range 256).filter (fun m => fixesT m) = fixedL :=
  beq_iff_eq.mp (by decide +kernel : ((List.range 256).filter (fun m => fixesT m) == fixedL) = true)

end CFSG.RankThree.GF2n.Parrott.SpinRigid.HbadTPack
