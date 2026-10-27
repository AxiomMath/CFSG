module

public import Certificates.Data.Kernel.Misc.YamakiA0
public import Certificates.Data.Z6NACount

public section

namespace CFSG.KD.YamakiLbar

open CFSG.KD.BfsK CFSG.KC.Loop CFSG.ClassicalInvolution.Sp62Rec
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def crd (Q : Nat → Nat) (k : Nat) : Nat := Q (Nat.add 12 k)

@[expose] noncomputable def psc (Q : Nat → Nat) (c : Nat) : Nat := Q (Nat.add 76 c)

@[expose] noncomputable def lbL (Q : Nat → Nat) (t : Nat) : Nat := recX Q 140 t

@[expose] noncomputable def stL (Q : Nat → Nat) (x s : Nat) : Nat := MULF (Q (Nat.mul s 11)) x

@[expose] noncomputable def coordK (R Q : Nat → Nat) : Bool :=
  Nat.beq (crd Q 0) 0 &&
  allBelow 64 1 (fun k => Nat.blt (crd Q k) 64 && Nat.beq (psc Q (crd Q k)) k &&
    Nat.blt (psc Q k) 64 && Nat.beq (crd Q (psc Q k)) k) &&
  allBelow 384 6 (fun i => Nat.beq (crd Q (recPOS R 12 6 i))
    (Nat.xor (crd Q (Nat.div i 6)) (Nat.shiftLeft 1 (Nat.mod i 6))))

@[expose] noncomputable def glK (R Q : Nat → Nat) : Bool :=
  allBelow 11 1 fun i => Nat.beq (MULF (R i) (R i)) ONE && allBelow 6 1 fun j =>
    Nat.beq (MULF (MULF (R i) (R (Nat.add j 3))) (R i))
      (recX R 12 (psc Q (MULF (Nat.shiftLeft 1 j) (Q i))))

@[expose] noncomputable def lbTabK (Q : Nat → Nat) : Bool :=
  Nat.beq (lbL Q 0) ONE && Nat.beq (Q 11) (MULF (Q 10) (Q 9)) &&
    tableKk Q (stL Q) 140 168 2 3 6 3

@[expose] noncomputable def lbMemK (Q : Nat → Nat) : Bool :=
  Nat.beq (MULF (Q 0) (Q 0)) ONE && Nat.beq (MULF (MULF (Q 11) (Q 11)) (Q 11)) ONE &&
    allBelow 11 1 fun i => Nat.blt (Q (Nat.add 309 i)) 168 &&
      Nat.beq (lbL Q (Q (Nat.add 309 i))) (Q i)

@[expose] noncomputable def rowsW (Λ : Nat → Nat) (c : Nat) : List Nat :=
  z6J.map fun J => J.foldr (fun m a => Nat.xor (MULF c (Λ m)) a) 0

@[expose] noncomputable def packL (rs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.add r (Nat.mul 64 ih)) rs

@[expose] noncomputable def boolN (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def rowS (S i : Nat) : Nat :=
  Nat.land (Nat.shiftRight S (Nat.mul 6 i)) 63

@[expose] noncomputable def vmul (r S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i ih => Nat.xor ih (cond (Nat.beq (Nat.land (Nat.shiftRight r i) 1) 1) (rowS S i) 0)) 6

@[expose] noncomputable def trK (x : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor x (Nat.shiftRight x 7))
    (Nat.shiftRight x 14)) (Nat.shiftRight x 21)) (Nat.shiftRight x 28)) (Nat.shiftRight x 35)) 1

@[expose] noncomputable def gmat6 (r S0 S1 S2 S3 S4 S5 : Nat) : Nat :=
  packL [vmul r S0, vmul r S1, vmul r S2, vmul r S3, vmul r S4, vmul r S5]

@[expose] noncomputable def treeK (Q : Nat → Nat) : Bool :=
  [(0, 0, 0), (1, 0, 1), (2, 1, 1), (3, 2, 0), (4, 2, 1), (7, 4, 1), (8, 5, 0), (13, 9, 1)].all
    fun e => Nat.beq (recF Q 140 0 e.1) e.2.1 && Nat.beq (recF Q 140 1 e.1) e.2.2

@[expose] noncomputable def witOK (Q : Nat → Nat) (w G : Nat) : Bool :=
  (Nat.blt 0 w && Nat.blt w 169 && Nat.beq (lbL Q (Nat.pred w)) G) ||
    (Nat.blt 1000 w && Nat.blt w 1064 && Nat.beq (MULF (Nat.sub w 1000) G) 0)

@[expose] noncomputable def candG (Q : Nat → Nat) (w TA TB G : Nat) : Bool :=
  !(Nat.beq (MULF (Q 0) G) (MULF G TA) && Nat.beq (MULF (Q 11) G) (MULF G TB)) || witOK Q w G

@[expose] noncomputable def candP (Q W : Nat → Nat) (p TA TB : Nat) : Bool :=
  boolN (MULF TA TB) fun l4 => !Nat.beq (trK l4) 1 ||
  (boolN (MULF TB TA) fun l3 => boolN (MULF TB TB) fun l5 =>
  boolN (MULF TB l4) fun l8 => boolN (MULF TA l5) fun l9 => boolN (MULF TB l9) fun l14 =>
  boolN (Nat.xor ONE (Nat.xor l5 l14)) fun S0 => boolN (Nat.xor ONE (Nat.xor TB l3)) fun S1 =>
  boolN (Nat.xor TB (Nat.xor l5 l8)) fun S3 =>
  allBelow 4 1 fun ρ => candG Q (W (Nat.add (Nat.mul 4 p) ρ)) TA TB
    (gmat6 (Q (Nat.add 735 ρ)) S0 S1 ONE S3 TB l5))

@[expose] noncomputable def candK (Q W : Nat → Nat) : Bool :=
  Nat.beq (trK (MULF (Q 0) (Q 11))) 1 &&
  allBelow 1254 20 fun p => candP Q W p (lbL Q (Q (Nat.add 320 (Nat.div p 57))))
    (lbL Q (Q (Nat.add 342 (Nat.mod p 57))))

@[expose] noncomputable def orbK (Q : Nat → Nat) : Bool :=
  decide (rowsW (lbL Q) (crd Q 3) = [1, 2, 4, 8, 16, 32])

@[expose] noncomputable def iaK (Q : Nat → Nat) : Bool :=
  allBelow 168 3 fun t => !Nat.beq (MULF (lbL Q t) (lbL Q t)) ONE ||
    (Nat.blt (Q (Nat.add 399 t)) 22 && Nat.beq (Q (Nat.add 320 (Q (Nat.add 399 t)))) t)

@[expose] noncomputable def ibK (Q : Nat → Nat) : Bool :=
  allBelow 168 3 fun t => !Nat.beq (MULF (MULF (lbL Q t) (lbL Q t)) (lbL Q t)) ONE ||
    (Nat.blt (Q (Nat.add 567 t)) 57 && Nat.beq (Q (Nat.add 342 (Q (Nat.add 567 t)))) t)

@[expose] noncomputable def repOne (Q : Nat → Nat) (c : Nat) : Bool :=
  Nat.blt (Q (Nat.add 739 c)) 4 && Nat.blt (Q (Nat.add 803 c)) 168 &&
    Nat.blt (Q (Nat.add 867 c)) 168 &&
    Nat.beq (MULF (lbL Q (Q (Nat.add 803 c))) (lbL Q (Q (Nat.add 867 c)))) ONE &&
    Nat.beq (MULF c (lbL Q (Q (Nat.add 803 c)))) (Q (Nat.add 735 (Q (Nat.add 739 c))))

@[expose] noncomputable def repK (Q : Nat → Nat) : Bool :=
  allBelow 63 1 fun c => repOne Q (Nat.succ c)

end CFSG.KD.YamakiLbar

end
