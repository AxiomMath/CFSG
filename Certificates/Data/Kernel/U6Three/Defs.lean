module

public import Certificates.Data.U6ThreeRank

public section

namespace CFSG.KC.U6Three

open CFSG.RankThree.PartOne.F106

@[expose] def enc (x : U6Mon) : Nat :=
  x.d0.val + 3 * (x.d1.val + 3 * (x.d2.val + 3 * (x.d3.val + 3 * (x.d4.val + 3 * (x.d5.val +
    3 * (x.t0.val + 3 * x.t1.val))))))

@[expose] def dig (c m : Nat) : Nat := c / 3 ^ m % 3

@[expose] def pk (a k : Nat) : Nat := 3 * (k / 3) + (k % 3 + 2 * dig a (6 + k / 3)) % 3

@[expose] def rawN (a b k : Nat) : Nat := (dig a k + dig b (pk a k)) % 3

@[expose] def outD (a b k : Nat) : Nat := (rawN a b k + 2 * rawN a b 0) % 3

@[expose] def mulN (a b : Nat) : Nat :=
  outD a b 0 + 3 * (outD a b 1 + 3 * (outD a b 2 + 3 * (outD a b 3 + 3 * (outD a b 4 +
    3 * (outD a b 5 + 3 * ((dig a 6 + dig b 6) % 3 + 3 * ((dig a 7 + dig b 7) % 3)))))))

@[expose] def genC (k : Nat) : Nat := [489, 495, 513, 567, 729, 2187].getD k 0

@[expose] def lk13 (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 13 i)) 8191

@[expose] def lk10 (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 10 i)) 1023

@[expose] noncomputable def tabN (TP i : Nat) : Nat := Bool.rec 0 (lk13 TP i) (Nat.blt i 729)

@[expose] noncomputable def invN (IP i : Nat) : Nat := Bool.rec 0 (lk10 IP i) (Nat.blt i 729)

@[expose] noncomputable def wordN (w : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a) (fun k _ ih a => ih (mulN a (genC k))) w acc

@[expose] noncomputable def allIdx {α : Type} (p : Nat → α → Bool) (L : List α) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun a _ ih n => p n a && ih (n + 1)) L n

@[expose] noncomputable def natAll (p : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => p k && ih) n

@[expose] noncomputable def commN (TP a b : Nat) : Bool :=
  Nat.beq (mulN (tabN TP a) (tabN TP b)) (mulN (tabN TP b) (tabN TP a))

@[expose] noncomputable def conjN (TP IP i u : Nat) : Nat :=
  mulN (mulN (tabN TP u) (tabN TP i)) (tabN TP (invN IP u))

@[expose] noncomputable def witN (TP IP : Nat) (zl : List Nat) (i : Nat) (w : Wit) : Bool :=
  Wit.rec (motive := fun _ => Bool) (decide (i ∈ zl))
    (fun u₀ u₁ u₂ u₃ => decide (u₀ < 729 ∧ u₁ < 729 ∧ u₂ < 729 ∧ u₃ < 729) &&
      decide [conjN TP IP i u₀, conjN TP IP i u₁, conjN TP IP i u₂, conjN TP IP i u₃].Nodup)
    (fun z x y => decide (z < 729 ∧ x < 729 ∧ y < 729) && !commN TP z i && commN TP x i &&
      commN TP y i && !commN TP x y)
    (fun z x => decide (z < 729 ∧ x < 729) && !commN TP z i && commN TP x i &&
      !Nat.beq (mulN (mulN (tabN TP x) (tabN TP x)) (tabN TP x)) 0)
    w

@[expose] noncomputable def chkTab (TP : Nat) (paths : List (List Nat)) : Bool :=
  allIdx (fun i w => Nat.beq (lk13 TP i) (wordN w 0)) paths 0

@[expose] noncomputable def chkInj (TP JP : Nat) : Bool :=
  natAll (fun i => Nat.beq (lk10 JP (lk13 TP i)) i) 729

@[expose] noncomputable def chkInv (TP IP : Nat) (inv : List Nat) : Bool :=
  allIdx (fun i v => Nat.beq (lk10 IP i) v && Nat.blt v 729 &&
    Nat.beq (mulN (tabN TP i) (tabN TP v)) 0) inv 0

@[expose] noncomputable def chkRt (TP : Nat) (rt : List Nat) : Bool :=
  allIdx (fun n r => Nat.blt r 729 &&
    Nat.beq (mulN (tabN TP (n / 6)) (genC (n % 6))) (tabN TP r)) rt 0

@[expose] noncomputable def chkWit (TP IP : Nat) (zl : List Nat) (wit : List Wit) : Bool :=
  allIdx (witN TP IP zl) wit 0

end CFSG.KC.U6Three
