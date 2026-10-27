module

public import Certificates.Data.Kernel.CoPair

public section

namespace CFSG.KC.CoPair

open CFSG.Monster.Existence.CoPair.Native

@[expose] noncomputable def f16 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 16)) 65535

@[expose] noncomputable def bword (TX TY : Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun g _ ih v => ih (bact (Bool.rec (motive := fun _ => Nat) TY TX (Nat.beq g 0)) v)) w v

@[expose] noncomputable def rowsW (M TX TY : Nat) (w : List Nat) : Bool :=
  allN 24 fun i => Nat.beq (f24 M i) (bword TX TY w (Nat.shiftLeft 1 i))

@[expose] noncomputable def eqPt (TA TB Q L SA SB m n i : Nat) : Bool :=
  letB (f24 Q i) fun v => letB (f64 L i) fun r =>
    andB (Nat.blt (r16 r 0) m) <| andB (Nat.beq (f24 Q (r16 r 0)) (bact TA v)) <|
    andB (Nat.blt (r16 r 1) m) <| andB (Nat.beq (f24 Q (r16 r 1)) (bact TB v)) <|
    andB (Nat.blt (r16 r 2) n) <|
    andB (Nat.beq (r16 (f64 L (r16 r 0)) 2) (f16 SA (r16 r 2))) <|
    andB (Nat.beq (r16 (f64 L (r16 r 1)) 2) (f16 SB (r16 r 2))) <|
      ifB (Nat.blt (Nat.succ i) m) (Nat.blt v (f24 Q (Nat.succ i))) true

@[expose] noncomputable def repPt (L R m j : Nat) : Bool :=
  letB (f16 R j) fun k => andB (Nat.blt k m) (Nat.beq (r16 (f64 L k) 2) j)

structure EqData where
  MX : Nat
  MY : Nat
  TX : Nat
  TY : Nat
  MA : Nat
  MB : Nat
  TA : Nat
  TB : Nat
  Q : Nat
  L : Nat
  R : Nat
  SA : Nat
  SB : Nat
  m : Nat

@[expose] noncomputable def eqOK (a b : List Nat) (w n : Nat) (D : EqData) : Bool :=
  andB (rowsOK D.MX (xWordN ())) <| andB (rowsOK D.MY (yWordN ())) <| andB (tabOK D.MX D.TX) <|
    andB (tabOK D.MY D.TY) <| andB (rowsW D.MA D.TX D.TY a) <| andB (rowsW D.MB D.TX D.TY b) <|
    andB (tabOK D.MA D.TA) <| andB (tabOK D.MB D.TB) <| andB (Nat.blt w 16777216) <|
    andB (Nat.beq (bact D.TA w) w) <| andB (Nat.beq (bact D.TB w) w) <|
    andB (allN D.m (eqPt D.TA D.TB D.Q D.L D.SA D.SB D.m n)) (allN n (repPt D.L D.R D.m))

end CFSG.KC.CoPair

end
