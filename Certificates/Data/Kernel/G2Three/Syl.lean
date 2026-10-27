module

public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def allL (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(p x, ih)) l

@[expose] def parL (PA PB : Nat → Nat) (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (PA i, PB i)

@[expose] noncomputable def closeK (X G POS : Nat → Nat) (n k hi : Nat) : Bool :=
  allBelow (Nat.mul n k) hi fun i =>
    Nat.blt (POS i) n && Nat.beq (X (POS i)) (MUL (X (Nat.div i k)) (G (Nat.mod i k)))

@[expose] noncomputable def letK (A : Nat → Nat) (l : Nat) : Nat :=
  cond (Nat.blt l 4) (A l) (cond (Nat.blt l 8) (MUL (A (Nat.sub l 4)) (A (Nat.sub l 4)))
    (MUL ONE ONE))

@[expose] noncomputable def wordK (A : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc l => MUL acc (letK A l)) ONE

@[expose] noncomputable def pwK (E k : Nat) : Nat :=
  cond (Nat.beq k 0) ONE (cond (Nat.beq k 1) E (MUL E E))

@[expose] noncomputable def dPK (E : Nat → Nat) (u : Nat) : Nat :=
  MUL (MUL (MUL (pwK (E 0) (Nat.mod u 3)) (pwK (E 1) (Nat.mod (Nat.div u 3) 3)))
    (pwK (E 2) (Nat.mod (Nat.div u 9) 3))) (pwK (E 3) (Nat.mod (Nat.div u 27) 3))

@[expose] noncomputable def lPK (E : Nat → Nat) (u : Nat) : Nat :=
  MUL (MUL (pwK (E 0) (Nat.mod u 3)) (pwK (E 1) (Nat.mod (Nat.div u 3) 3)))
    (pwK (E 2) (Nat.mod (Nat.div u 9) 3))

@[expose] noncomputable def commK2 (A B : Nat) : Bool := Nat.beq (MUL A B) (MUL B A)

@[expose] noncomputable def cubeK2 (A : Nat) : Bool := Nat.beq (MUL A (MUL A A)) ONE

@[expose] noncomputable def dBlockK (X DX SRT SRI ZW : Nat → Nat) (D : List Nat) (z j : Nat) :
    Bool :=
  (fun E : Nat → Nat =>
    allBelow 4 1 (fun a => allBelow 4 1 fun b => commK2 (E a) (E b)) &&
    allBelow 4 1 (fun a => cubeK2 (E a)) &&
    allBelow 81 2 (fun u => Nat.beq (DX (Nat.add (Nat.mul 81 j) u)) (dPK E u)) &&
    sortK (fun u => DX (Nat.add (Nat.mul 81 j) u)) (fun u => SRT (Nat.add (Nat.mul 81 j) u))
      (fun u => SRI (Nat.add (Nat.mul 81 j) u)) 81 2 &&
    Nat.blt (ZW j) 81 && Nat.beq (DX (Nat.add (Nat.mul 81 j) (ZW j))) (X z))
  (fun a => X (D.getD a 0))

@[expose] noncomputable def witK (X DX W : Nat → Nat) (n m hi : Nat) : Bool :=
  allBelow n hi fun t =>
    Nat.beq (X t) ONE || !(cubeK2 (X t)) || (Nat.blt (W t) m && Nat.beq (DX (W t)) (X t))

@[expose] noncomputable def inTK (TKY TDR : Nat → Nat) (M D : Nat) : Bool :=
  (fun j => Nat.blt j 200 && Nat.beq D (TDR j)) (TKY (Nat.mod D M))

@[expose] noncomputable def isNK (X : Nat → Nat) (inT : Nat → Bool) (t : Nat) : Bool :=
  !(Nat.beq (X t) ONE) && cubeK2 (X t) && !(inT (X t))

@[expose] noncomputable def fR (R k : Nat) : Nat := Nat.land (Nat.shiftRight R (Nat.mul 10 k)) 1023

@[expose] noncomputable def pA (PP k : Nat) : Nat := Nat.land (Nat.shiftRight PP (Nat.mul 12 k)) 1023

@[expose] noncomputable def pB (PP k : Nat) : Nat :=
  Nat.land (Nat.shiftRight PP (Nat.add (Nat.mul 12 k) 10)) 3

@[expose] noncomputable def bitK (B t : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight B t) 1) 1

@[expose] noncomputable def rowK (PP RTP R : Nat) : Bool :=
  allBelow 728 12 fun k =>
    Nat.beq (fR R (Nat.succ k)) (fR RTP (Nat.add (Nat.mul 3 (fR R (pA PP k))) (pB PP k)))

@[expose] noncomputable def pairK (RO RI : List Nat) (TB : Nat) : Bool :=
  allL (fun RA => (fun a => (fun aa => allL (fun RB => (fun b =>
    Nat.beq b a || Nat.beq b aa || (fun ab => !(Nat.beq ab (fR RB a)) || bitK TB ab ||
      bitK TB (fR RA (fR RB b))) (fR RA b)) (fR RB 0)) RI) (fR RA a)) (fR RA 0)) RO

end CFSG.KD.G2Three

end
