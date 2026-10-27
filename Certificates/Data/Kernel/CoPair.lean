module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPair

public section

namespace CFSG.KC.CoPair

open CFSG.Monster.Existence.CoPair.Native

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def ifB (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def allR (lo n : Nat) (f : Nat → Bool) : Bool :=
  allN n fun i => f (Nat.add lo i)

@[expose] noncomputable def f24 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 24)) 16777215

@[expose] noncomputable def f64 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 64)) 18446744073709551615

@[expose] noncomputable def r16 (r j : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul j 16)) 65535

@[expose] noncomputable def actM (M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.xor acc
    (Bool.rec (motive := fun _ => Nat) 0 (f24 M i) (Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 i)))))
    24

@[expose] noncomputable def bact (T v : Nat) : Nat :=
  Nat.xor (f24 T (Nat.land v 255)) (Nat.xor (f24 T (Nat.add 256 (Nat.land (Nat.shiftRight v 8) 255)))
    (f24 T (Nat.add 512 (Nat.land (Nat.shiftRight v 16) 255))))

@[expose] noncomputable def rowsOK (M : Nat) (w : List Nat) : Bool :=
  allN 24 fun i => Nat.beq (f24 M i) (actLetters w (Nat.shiftLeft 1 i))

@[expose] noncomputable def tabOK (M T : Nat) : Bool :=
  allN 768 fun j =>
    Nat.beq (f24 T j) (actM M (Nat.shiftLeft (Nat.land j 255) (Nat.mul 8 (Nat.shiftRight j 8))))

@[expose] noncomputable def orbPt (TX TY P E N s i : Nat) : Bool :=
  letB (f24 P i) fun v => letB (f64 E i) fun r =>
    andB (Nat.blt (r16 r 0) N) <| andB (Nat.beq (f24 P (r16 r 0)) (bact TX v)) <|
    andB (Nat.blt (r16 r 1) N) <| andB (Nat.beq (f24 P (r16 r 1)) (bact TY v)) <|
    andB (ifB (Nat.blt (Nat.succ i) N) (Nat.blt v (f24 P (Nat.succ i))) true) <|
    ifB (Nat.beq (r16 r 3) 0) (Nat.beq i s) <|
      letB (r16 r 2) fun p => andB (Nat.blt p N) <| letB (f64 E p) fun q =>
        andB (Nat.blt (r16 q 3) (r16 r 3)) (orB (Nat.beq (r16 q 0) i) (Nat.beq (r16 q 1) i))

structure OrbData where
  MX : Nat
  MY : Nat
  TX : Nat
  TY : Nat
  P : Nat
  E : Nat
  s : Nat

@[expose] noncomputable def orbOK (wx wy : List Nat) (seed N : Nat) (D : OrbData) : Bool :=
  andB (rowsOK D.MX wx) <| andB (rowsOK D.MY wy) <| andB (tabOK D.MX D.TX) <|
    andB (tabOK D.MY D.TY) <| andB (Nat.blt D.s N) <| andB (Nat.beq (f24 D.P D.s) seed) <|
      allN N (orbPt D.TX D.TY D.P D.E N D.s)

end CFSG.KC.CoPair

end
