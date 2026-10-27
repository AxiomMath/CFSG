module

public import Certificates.Data.Kernel.FiveStdKTree

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def f96 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 96)) 79228162514264337593543950335

@[expose] noncomputable def oCode (r : Nat) : Nat := Nat.land r 1048575
@[expose] noncomputable def oPar (r : Nat) : Nat := Nat.land (Nat.shiftRight r 20) 4095
@[expose] noncomputable def oLet (r : Nat) : Nat := Nat.land (Nat.shiftRight r 32) 15
@[expose] noncomputable def oDep (r : Nat) : Nat := Nat.land (Nat.shiftRight r 36) 255
@[expose] noncomputable def oNx (r l : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.add 44 (Nat.mul 12 l))) 4095

@[expose] noncomputable def cjK (g gi x : Nat) : Nat := mulK (mulK g x) gi

@[expose] noncomputable def oPt (G GI nG R M root j : Nat) : Bool :=
  letB (f96 R j) fun r => letB (oCode r) fun c =>
    andB (ifB (Nat.blt (Nat.succ j) M) (Nat.blt c (oCode (f96 R (Nat.succ j)))) true) <|
    andB (allN nG fun l => letB (oNx r l) fun n =>
      andB (Nat.blt n M) (Nat.beq (oCode (f96 R n)) (cjK (f20 G l) (f20 GI l) c))) <|
    ifB (Nat.beq (oDep r) 0) (Nat.beq c root) <|
      letB (oPar r) fun p => letB (oLet r) fun l => letB (f96 R p) fun rp =>
        andB (Nat.blt p M) <| andB (Nat.blt l nG) <| andB (Nat.blt (oDep rp) (oDep r)) <|
          Nat.beq (cjK (f20 G l) (f20 GI l) (oCode rp)) c

@[expose] noncomputable def cPt (B g M k : Nat) : Bool :=
  letB (f20 B k) fun b =>
    andB (validK b) <|
    andB (ifB (Nat.blt (Nat.succ k) M) (Nat.blt b (f20 B (Nat.succ k))) true) <|
      Nat.beq (mulK b g) (mulK g b)

@[expose] noncomputable def genOK (G GI nG : Nat) : Bool :=
  allN nG fun l => andB (validK (f20 G l)) (Nat.beq (mulK (f20 G l) (f20 GI l)) oneK)

@[expose] noncomputable def clsOK (G GI nG g R M B Mc v : Nat) : Bool :=
  andB (genOK G GI nG) <| andB (validK g) <| andB (Nat.blt 0 M) <|
  andB (allN M (oPt G GI nG R M g)) <| andB (allN Mc (cPt B g Mc)) <|
    andB (validK v) (Nat.beq (cjK v (invK v) g) (invK g))

end CFSG.KC.FiveStdK

end
