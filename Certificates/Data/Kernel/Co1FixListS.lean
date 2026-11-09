module

public import Certificates.Data.Kernel.Co1FixList

public section

namespace CFSG.KC.Co1Fix

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Loop

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem fget_zero (i w : Nat) : fget 0 i w = 0 := by
  unfold fget
  show (0 >>> (i * w)) &&& maskN w = 0
  rw [Nat.zero_shiftRight]
  exact Nat.zero_and _

theorem bit_zero (j : Nat) : bit 0 j = false := by
  unfold bit
  have h : Nat.land (Nat.shiftRight 0 j) 1 = 0 := by
    show (0 >>> j) &&& 1 = 0
    rw [Nat.zero_shiftRight]
    rfl
  rw [h]
  rfl

theorem vmF_zero (d v : Nat) : vmF d 0 v = 0 := by
  unfold vmF
  have : ∀ n : Nat, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => nIf(bit v k, Nat.xor (rowF d 0 k) acc, acc)) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show Bool.rec (motive := fun _ => Nat) _ _ (bit v k) = 0
      rw [ih]
      cases bit v k
      · rfl
      · show Nat.xor (fget 0 k d) 0 = 0
        rw [fget_zero]
        rfl
  exact this d

theorem dotK_zero (d x : Nat) : dotK d x 0 = false := by
  unfold dotK
  induction d with
  | zero => rfl
  | succ j ih =>
    show Bool.rec (motive := fun _ => Bool) _ _ (andB (bit x j) (bit 0 j)) = false
    rw [bit_zero]
    cases bit x j <;> exact ih

theorem qCountK_zero (d : Nat) (F : List Nat) (acc : Nat) : qCountK d 0 F acc = 0 := by
  induction F generalizing acc with
  | nil =>
    show Bool.rec (motive := fun _ => Nat) 0 1 (dotK d acc (vecK d 0 acc)) = 0
    rw [show vecK d 0 acc = 0 from vmF_zero d acc, dotK_zero]
  | cons f F ih =>
    show strictN (qCountK d 0 F acc)
      (fun a => strictN (qCountK d 0 F (Nat.xor acc f)) fun b => Nat.add a b) = 0
    rw [strictN_eq, strictN_eq, ih, ih]

theorem qCountK_consS (d Qt f : Nat) (G : List Nat) (acc : Nat) :
    qCountK d Qt (f :: G) acc = Nat.add (qCountK d Qt G acc) (qCountK d Qt G (Nat.xor acc f)) := by
  show strictN (qCountK d Qt G acc)
    (fun a => strictN (qCountK d Qt G (Nat.xor acc f)) fun b => Nat.add a b) = _
  rw [strictN_eq, strictN_eq]

theorem qCountK_split2 (d Qt : Nat) (acc : Nat) : ∀ (F : List Nat), 2 ≤ F.length →
    qCountK d Qt F acc =
      Nat.add (Nat.add (qCountK d Qt (F.drop 2) acc) (qCountK d Qt (F.drop 2) (Nat.xor acc (F.getD 1 0))))
        (Nat.add (qCountK d Qt (F.drop 2) (Nat.xor acc (F.getD 0 0)))
          (qCountK d Qt (F.drop 2) (Nat.xor (Nat.xor acc (F.getD 0 0)) (F.getD 1 0))))
  | f1 :: f2 :: G, _ => by
    rw [qCountK_consS, qCountK_consS, qCountK_consS]
    rfl

@[expose] noncomputable def fixHead (TA TB : Nat) (W : List Nat) : Bool :=
  CFSG.Sporadic.Co1.OddNative.strictInc W &&
    W.all (fun x => decide (x < 2 ^ 24) && vmF 24 TA x == x && vmF 24 TB x == x)

@[expose] noncomputable def fixP (TB : Nat) (W : List Nat) (y : Nat) : Bool :=
  !(vmF 24 TB y == y) || W.contains y

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem all_spanK_cons (P : Nat → Bool) (f : Nat) (G : List Nat) (a : Nat) :
    (spanK (f :: G) a).all P = ((spanK G a).all P && (spanK G (a ^^^ f)).all P) := by
  rw [spanK, List.all_append]

theorem fixListK_split {TA TB : Nat} {W : List Nat} :
    ∀ {F : List Nat}, 2 ≤ F.length → fixHead TA TB W = true →
      (spanK (F.drop 2) 0).all (fixP TB W) = true →
      (spanK (F.drop 2) (0 ^^^ F.getD 1 0)).all (fixP TB W) = true →
      (spanK (F.drop 2) (0 ^^^ F.getD 0 0)).all (fixP TB W) = true →
      (spanK (F.drop 2) (0 ^^^ F.getD 0 0 ^^^ F.getD 1 0)).all (fixP TB W) = true →
      fixListK TA TB F W = true
  | f1 :: f2 :: G, _, h0, h1, h2, h3, h4 => by
    show (fixHead TA TB W && (spanK (f1 :: f2 :: G) 0).all (fixP TB W)) = true
    rw [all_spanK_cons, all_spanK_cons, all_spanK_cons, h0]
    exact andT rfl (andT (andT h1 h2) (andT h3 h4))

end CFSG.KC.Co1Fix

end
