module

public import Init

public section

namespace CFSG.KC.WeylE6

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def ifB (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def allR (lo n : Nat) (f : Nat → Bool) : Bool :=
  allN n fun i => f (Nat.add lo i)

@[expose] noncomputable def f8 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul i 8)) 255

@[expose] noncomputable def f48 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 48)) 281474976710655

@[expose] noncomputable def f112 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 112)) 5192296858534827628530496329220095

@[expose] noncomputable def r16 (r j : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.mul j 16)) 65535

@[expose] noncomputable def keyOf (w : Nat) : Nat := Nat.land w 1099511627775

@[expose] noncomputable def levOf (w : Nat) : Nat := Nat.shiftRight w 40

@[expose] noncomputable def idKey : Nat := 348345926401

@[expose] noncomputable def validK (v : Nat) : Bool :=
  andB (Nat.blt (f8 v 0) 243) <| andB (Nat.blt (f8 v 1) 243) <| andB (Nat.blt (f8 v 2) 243) <|
    andB (Nat.blt (f8 v 3) 243) (Nat.blt (f8 v 4) 243)

@[expose] noncomputable def rowT (T t c : Nat) : Nat := f8 T (Nat.add (Nat.mul t 256) c)

@[expose] noncomputable def mulT (T t v : Nat) : Nat :=
  Nat.add (rowT T t (f8 v 0)) <| Nat.add (Nat.shiftLeft (rowT T t (f8 v 1)) 8) <|
    Nat.add (Nat.shiftLeft (rowT T t (f8 v 2)) 16) <|
      Nat.add (Nat.shiftLeft (rowT T t (f8 v 3)) 24) (Nat.shiftLeft (rowT T t (f8 v 4)) 32)

@[expose] noncomputable def wPt (T P E N i : Nat) : Bool :=
  letB (f48 P i) fun w => letB (keyOf w) fun v => letB (f112 E i) fun r =>
    andB (validK v) <|
    andB (allN 6 fun t => letB (r16 r t) fun n =>
      andB (Nat.blt n N) (Nat.beq (keyOf (f48 P n)) (mulT T t v))) <|
    andB (ifB (Nat.blt (Nat.succ i) N) (Nat.blt v (keyOf (f48 P (Nat.succ i)))) true) <|
    ifB (Nat.beq (levOf w) 0) (Nat.beq v idKey) <|
      letB (r16 r 6) fun g => andB (Nat.blt g 6) (Nat.blt (levOf (f48 P (r16 r g))) (levOf w))

@[expose] noncomputable def wOK (T P E N s : Nat) : Bool :=
  andB (Nat.blt s N) <| andB (Nat.beq (keyOf (f48 P s)) idKey) (allN N (wPt T P E N))

end CFSG.KC.WeylE6

end
