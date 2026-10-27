module

public import Init

public section

namespace CFSG.KC.Q9SL

@[expose] noncomputable def addF (x y : Nat) : Nat :=
  Nat.add (Nat.mul 3 (Nat.mod (Nat.add (Nat.div x 3) (Nat.div y 3)) 3))
    (Nat.mod (Nat.add (Nat.mod x 3) (Nat.mod y 3)) 3)

@[expose] noncomputable def subF (x y : Nat) : Nat :=
  Nat.add (Nat.mul 3 (Nat.mod (Nat.add (Nat.div x 3) (Nat.sub 3 (Nat.div y 3))) 3))
    (Nat.mod (Nat.add (Nat.mod x 3) (Nat.sub 3 (Nat.mod y 3))) 3)

@[expose] noncomputable def negF (x : Nat) : Nat := subF 0 x

@[expose] noncomputable def mulF (x y : Nat) : Nat :=
  Nat.add (Nat.mul 3 (Nat.mod (Nat.add (Nat.mul (Nat.div x 3) (Nat.div y 3))
      (Nat.mul 2 (Nat.mul (Nat.mod x 3) (Nat.mod y 3)))) 3))
    (Nat.mod (Nat.add (Nat.mul (Nat.div x 3) (Nat.mod y 3)) (Nat.mul (Nat.mod x 3) (Nat.div y 3))) 3)

@[expose] noncomputable def fl (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) 15

@[expose] noncomputable def pk (a b c d : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft a 12) (Nat.lor (Nat.shiftLeft b 8) (Nat.lor (Nat.shiftLeft c 4) d))

@[expose] noncomputable def m00 (x : Nat) : Nat := fl x 12
@[expose] noncomputable def m01 (x : Nat) : Nat := fl x 8
@[expose] noncomputable def m10 (x : Nat) : Nat := fl x 4
@[expose] noncomputable def m11 (x : Nat) : Nat := fl x 0

@[expose] noncomputable def mulE (p q r s a b e d : Nat) : Nat :=
  pk (addF (mulF p a) (mulF q e)) (addF (mulF p b) (mulF q d)) (addF (mulF r a) (mulF s e))
    (addF (mulF r b) (mulF s d))

@[expose] noncomputable def mulS (x y : Nat) : Nat :=
  mulE (m00 x) (m01 x) (m10 x) (m11 x) (m00 y) (m01 y) (m10 y) (m11 y)

@[expose] noncomputable def conjE (p q r s a b e d : Nat) : Nat :=
  (fun x00 x01 x10 x11 => pk (subF (mulF x00 s) (mulF x01 r)) (subF (mulF x01 p) (mulF x00 q))
      (subF (mulF x10 s) (mulF x11 r)) (subF (mulF x11 p) (mulF x10 q)))
    (addF (mulF p a) (mulF q e)) (addF (mulF p b) (mulF q d)) (addF (mulF r a) (mulF s e))
    (addF (mulF r b) (mulF s d))

@[expose] noncomputable def conjS (c x : Nat) : Nat :=
  conjE (m00 c) (m01 c) (m10 c) (m11 c) (m00 x) (m01 x) (m10 x) (m11 x)

@[expose] noncomputable def negS (x : Nat) : Nat :=
  pk (negF (m00 x)) (negF (m01 x)) (negF (m10 x)) (negF (m11 x))

@[expose] noncomputable def invS (x : Nat) : Nat := pk (m11 x) (negF (m01 x)) (negF (m10 x)) (m00 x)

@[expose] noncomputable def sigS (x : Nat) : Nat :=
  pk (m11 x) (mulF 4 (m10 x)) (mulF 7 (m01 x)) (m00 x)

@[expose] noncomputable def trS (x : Nat) : Nat := addF (m00 x) (m11 x)

@[expose] noncomputable def repE (t b c : Nat) : Nat :=
  (fun sq => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 6 5 (Nat.beq sq 1)) 4
        (Nat.beq sq 6)) 3 (Nat.beq t 0))
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 2 1
        (Nat.beq (Nat.land (Nat.shiftRight 79
          (Bool.rec (motive := fun _ => Nat) b c (Nat.beq b 0))) 1) 1))
      0 (Nat.beq (Nat.lor b c) 0))
    (Nat.beq sq 3)) (mulF t t)

@[expose] noncomputable def repS (x : Nat) : Nat := repE (trS x) (m01 x) (m10 x)

@[expose] noncomputable def swapC (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) j 1 (Nat.beq j 2)) 2
    (Nat.beq j 1)

@[expose] noncomputable def ordFE (j t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat) 10 5 (Nat.beq t 4))
            (Bool.rec (motive := fun _ => Nat) 10 5 (Nat.beq t 5)) (Nat.beq j 5))
          8 (Nat.beq j 4))
        4 (Nat.beq j 3))
      (Bool.rec (motive := fun _ => Nat) 6 3 (Nat.beq t 6)) (Nat.blt (Nat.sub j 1) 2))
    (Bool.rec (motive := fun _ => Nat) 2 1 (Nat.beq t 6)) (Nat.beq j 0)

@[expose] noncomputable def oneS : Nat := 12291

@[expose] noncomputable def moneS : Nat := 24582

@[expose] noncomputable def ordAux (x : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih p n => Bool.rec (motive := fun _ => Nat) (ih (mulS p x) (Nat.succ n)) n
      (Nat.beq p oneS)) k

@[expose] noncomputable def ordS (x : Nat) : Nat := ordAux x 16 x 1

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih (f x)) L

@[expose] noncomputable def cntL (L : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (f x)) L

@[expose] noncomputable def allI (L : List Nat) (f : Nat → Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ i)) (f i x)) L

@[expose] noncomputable def incL (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => Bool.rec (motive := fun _ => Bool) false (ih x) (Nat.blt p x)) L

@[expose] noncomputable def all2 (L : List Nat) (f : Nat → Nat → Bool) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ws => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws)
    (fun x _ ih ws => List.rec (motive := fun _ => Bool) false
      (fun w ws' _ => Bool.rec (motive := fun _ => Bool) false (ih ws') (f x w)) ws) L

@[expose] noncomputable def ln (P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 16 i)) 65535

@[expose] noncomputable def ckSort (L : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.beq (cntL L fun _ => true) 720) (incL L 0)

@[expose] noncomputable def ckLP (L : List Nat) (LP : Nat) : Bool :=
  allI L (fun i x => Nat.beq (ln LP i) x) 0

@[expose] noncomputable def ckRep (R : List Nat) (RP : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.beq (cntL R fun _ => true) 7)
    (allI R (fun j r => Bool.rec (motive := fun _ => Bool) false (Nat.beq (ln RP j) r)
      (Nat.beq (repS r) j)) 0)

@[expose] noncomputable def ckWit (L : List Nat) (LP RP : Nat) (W : List Nat) : Bool :=
  all2 L (fun x w => Bool.rec (motive := fun _ => Bool) false
    ((fun y r => Bool.rec (motive := fun _ => Bool) (Nat.beq y (negS r)) true (Nat.beq y r))
      (conjS (ln LP w) x) (ln RP (repS x)))
    (Nat.blt w 720)) W

@[expose] noncomputable def ckConj (L : List Nat) (RP : Nat) : Bool :=
  allL L fun d => allL [0, 1, 2, 3, 4, 5, 6] fun j =>
    (fun r => Bool.rec (motive := fun _ => Bool) false (Nat.beq (repS (conjS d (negS r))) j)
      (Nat.beq (repS (conjS d r)) j)) (ln RP j)

@[expose] noncomputable def ckNeg (L : List Nat) : Bool :=
  allL L fun x => Nat.beq (repS (negS x)) (repS x)

@[expose] noncomputable def ckSig (L : List Nat) : Bool :=
  allL L fun x => Nat.beq (repS (sigS x)) (swapC (repS x))

@[expose] noncomputable def ckInv (L : List Nat) : Bool :=
  allL L fun x => Nat.beq (repS (invS x)) (repS x)

@[expose] noncomputable def ckCnt (L : List Nat) : Bool :=
  allI [2, 80, 80, 90, 180, 144, 144] (fun j n => Nat.beq (cntL L fun x => Nat.beq (repS x) j) n) 0

@[expose] noncomputable def ckZero (L : List Nat) : Bool :=
  allL L fun x => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false
      (Nat.beq x moneS)) false (Nat.beq x oneS))
    (Bool.rec (motive := fun _ => Bool) (Nat.beq x moneS) true (Nat.beq x oneS))
    (Nat.beq (repS x) 0)

@[expose] noncomputable def ckOrd (L : List Nat) : Bool :=
  allL L fun x => Nat.beq (ordS x) (ordFE (repS x) (trS x))

end CFSG.KC.Q9SL
