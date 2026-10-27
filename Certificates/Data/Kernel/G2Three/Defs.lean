module

public import CFSG.Certificates.Kernel.Orders.Mat3

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 196) 1

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 14) 1

@[expose] noncomputable def CI : Nat := rep1 14 14

@[expose] noncomputable def ONE : Nat := rep1 15 14

@[expose] noncomputable def UP : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 14 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 14) i)))) 14

@[expose] noncomputable def MUL (a b : Nat) : Nat := mul3s 14 196 LO CI RM a b

@[expose] noncomputable def SQ6 (a : Nat) : Nat :=
  strictN (MUL a a) fun b => strictN (MUL b b) fun c => strictN (MUL c c) fun d =>
    strictN (MUL d d) fun e => strictN (MUL e e) fun f => MUL f f

@[expose] noncomputable def buildK (X G PA PB : Nat → Nat) (n k hi : Nat) : Bool :=
  allBelow (Nat.sub n 1) hi fun i =>
    Nat.ble (PA i) i && Nat.blt (PB i) k && Nat.beq (X (Nat.succ i)) (MUL (X (PA i)) (G (PB i)))

@[expose] noncomputable def stepK (X G PA PB C POS : Nat → Nat) (n k hi : Nat) : Bool :=
  Nat.beq (C 0) 1 && Nat.beq (C (Nat.mul n k)) n &&
  allBelow (Nat.mul n k) hi fun i =>
    Nat.blt (Nat.div i k) (C i) && Nat.ble (POS i) (C i) && Nat.blt (POS i) n &&
    Nat.beq (X (POS i)) (MUL (X (Nat.div i k)) (G (Nat.mod i k))) &&
    cond (Nat.beq (POS i) (C i))
      (Nat.beq (C (Nat.succ i)) (Nat.succ (C i)) && Nat.beq (PA (Nat.pred (C i))) (Nat.div i k) &&
        Nat.beq (PB (Nat.pred (C i))) (Nat.mod i k))
      (Nat.beq (C (Nat.succ i)) (C i))

@[expose] noncomputable def sortK (X SRT SRI : Nat → Nat) (n hi : Nat) : Bool :=
  allBelow n hi fun i =>
    Nat.blt (SRT i) n && Nat.blt (SRI i) n && Nat.beq (SRI (SRT i)) i && Nat.beq (SRT (SRI i)) i &&
    cond (Nat.blt (Nat.succ i) n) (Nat.blt (X (SRT i)) (X (SRT (Nat.succ i)))) true

@[expose] noncomputable def orbK (X GA GB OA OB : Nat → Nat) (n k hi : Nat) : Bool :=
  allBelow (Nat.sub n 1) hi fun i =>
    Nat.ble (OA i) i && Nat.blt (OB i) k &&
    Nat.beq (X (Nat.succ i)) (MUL (MUL (GA (OB i)) (X (OA i))) (GB (OB i)))

@[expose] noncomputable def invK (XS XO IDX : Nat → Nat) (nS nO hi : Nat) : Bool :=
  allBelow nS hi fun t =>
    cond (Nat.beq (MUL (XS t) (XS t)) ONE)
      (Nat.beq (XS t) ONE || (Nat.blt (IDX t) nO && Nat.beq (XO (IDX t)) (XS t))) true

@[expose] noncomputable def centK (X : Nat → Nat) (X1 U TC n hi : Nat) : Bool :=
  allBelow n hi fun t =>
    cond (Nat.beq (MUL (X t) X1) (MUL X1 (X t)) && Nat.beq (MUL (X t) U) (MUL U (X t)) &&
        Nat.beq (SQ6 (X t)) ONE)
      (Nat.beq (X t) ONE || Nat.beq (X t) TC) true

@[expose] noncomputable def commK (G : Nat → Nat) (TC k : Nat) : Bool :=
  allBelow k 1 fun s => Nat.beq (MUL (G s) TC) (MUL TC (G s))

@[expose] noncomputable def cubeK (B : Nat → Nat) (k : Nat) : Bool :=
  allBelow k 1 fun s => Nat.beq (MUL (B s) (MUL (B s) (B s))) ONE

@[expose] def digsF : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | f + 1, n, acc =>
    cond (Nat.blt n 10) (Char.ofNat (Nat.add 48 n) :: acc)
      (digsF f (Nat.div n 10) (Char.ofNat (Nat.add 48 (Nat.mod n 10)) :: acc))

@[expose] def digs (n : Nat) : List Char := digsF 20 n []

@[expose] def pieceChars (a b : Nat) : List Char := digs a ++ ',' :: digs b

end CFSG.KD.G2Three

end
