module

public import Certificates.Data.Kernel.SporLatOrbP

public section

namespace CFSG.KC.SLOrb

@[expose] def allNR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => f i && ih) n

@[expose] def rCode (r : Nat) : Nat := Nat.land r 340282366920938463463374607431768211455

@[expose] def rRow (l r : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.add 128 (Nat.mul 16 l))) 65535

@[expose] def rPar (r : Nat) : Nat := Nat.land (Nat.shiftRight r 160) 65535

@[expose] def rDep (r : Nat) : Nat := Nat.land (Nat.shiftRight r 176) 255

@[expose] def rVia (r : Nat) : Nat := Nat.land (Nat.shiftRight r 184) 255

@[expose] def recOK (actF : Nat → Nat → Nat) (R : Nat → Nat) (n z i : Nat) : Bool :=
  (Nat.ble n (Nat.succ i) || Nat.blt (rCode (R i)) (rCode (R (Nat.succ i)))) &&
  Nat.blt (rRow 0 (R i)) n && Nat.beq (rCode (R (rRow 0 (R i)))) (actF 0 (rCode (R i))) &&
  Nat.blt (rRow 1 (R i)) n && Nat.beq (rCode (R (rRow 1 (R i)))) (actF 1 (rCode (R i))) &&
  (bif Nat.beq (rDep (R i)) 0 then Nat.beq (rCode (R i)) z
   else Nat.blt (rPar (R i)) n && Nat.blt (rVia (R i)) 2 &&
    Nat.beq (Nat.succ (rDep (R (rPar (R i))))) (rDep (R i)) &&
    Nat.beq (rRow (rVia (R i)) (R (rPar (R i)))) i)

@[expose] def orbRec (actF : Nat → Nat → Nat) (R : Nat → Nat) (n z iz : Nat) : Bool :=
  Nat.blt iz n && Nat.beq (rCode (R iz)) z && allNR n (recOK actF R n z)

@[expose] def gPr (w T p : Nat) : Nat := Nat.mod (Nat.div T (Nat.pow 2 (Nat.mul w p))) (Nat.pow 2 w)

@[expose] def pk1 (a r : Nat) : Nat := Nat.add a (Nat.mul 32 r)

@[expose] def pack23 (e : Nat → Nat) : Nat :=
  pk1 (e 0) <| pk1 (e 1) <| pk1 (e 2) <| pk1 (e 3) <| pk1 (e 4) <| pk1 (e 5) <| pk1 (e 6) <|
  pk1 (e 7) <| pk1 (e 8) <| pk1 (e 9) <| pk1 (e 10) <| pk1 (e 11) <| pk1 (e 12) <| pk1 (e 13) <|
  pk1 (e 14) <| pk1 (e 15) <| pk1 (e 16) <| pk1 (e 17) <| pk1 (e 18) <| pk1 (e 19) <|
  pk1 (e 20) <| pk1 (e 21) <| pk1 (e 22) 0

@[expose] def pack24 (e : Nat → Nat) : Nat :=
  pk1 (e 0) <| pk1 (e 1) <| pk1 (e 2) <| pk1 (e 3) <| pk1 (e 4) <| pk1 (e 5) <| pk1 (e 6) <|
  pk1 (e 7) <| pk1 (e 8) <| pk1 (e 9) <| pk1 (e 10) <| pk1 (e 11) <| pk1 (e 12) <| pk1 (e 13) <|
  pk1 (e 14) <| pk1 (e 15) <| pk1 (e 16) <| pk1 (e 17) <| pk1 (e 18) <| pk1 (e 19) <|
  pk1 (e 20) <| pk1 (e 21) <| pk1 (e 22) <| pk1 (e 23) 0

@[expose] def actN23 (Ls : List (Nat × Nat)) (l T : Nat) : Nat :=
  pack23 fun q => gPr 5 (Ls.getD l (0, 0)).1 (gPr 5 T (gPr 5 (Ls.getD l (0, 0)).2 q))

@[expose] def actN24 (Ls : List (Nat × Nat)) (l T : Nat) : Nat :=
  pack24 fun q => gPr 5 (Ls.getD l (0, 0)).1 (gPr 5 T (gPr 5 (Ls.getD l (0, 0)).2 q))

theorem actS_eqN23 (Ls : List (Nat × Nat)) (l T : Nat) : actS 5 23 Ls l [T] = [actN23 Ls l T] :=
  rfl

theorem actS_eqN24 (Ls : List (Nat × Nat)) (l T : Nat) : actS 5 24 Ls l [T] = [actN24 Ls l T] :=
  rfl

end CFSG.KC.SLOrb

end
