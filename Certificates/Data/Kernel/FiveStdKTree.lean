module

public import Certificates.Data.Kernel.FiveStdK

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def allR (lo n : Nat) (f : Nat → Bool) : Bool :=
  allN n fun i => f (Nat.add lo i)

@[expose] noncomputable def f64 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i 64)) 18446744073709551615

@[expose] noncomputable def f20 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul i 20)) 1048575

@[expose] noncomputable def rCode (r : Nat) : Nat := Nat.land r 1048575

@[expose] noncomputable def rPar (r : Nat) : Nat := Nat.land (Nat.shiftRight r 20) 32767

@[expose] noncomputable def rLet (r : Nat) : Nat := Nat.land (Nat.shiftRight r 35) 31

@[expose] noncomputable def rDep (r : Nat) : Nat := Nat.shiftRight r 40

@[expose] noncomputable def tPt (T G nG N i : Nat) : Bool :=
  letB (f64 T i) fun r => letB (rCode r) fun c =>
    andB (ifB (Nat.blt (Nat.succ i) N) (Nat.blt c (rCode (f64 T (Nat.succ i)))) true) <|
    ifB (Nat.beq (rDep r) 0) (Nat.beq c oneK) <|
      letB (rPar r) fun p => letB (f64 T p) fun rp =>
        andB (Nat.blt p N) <| andB (Nat.blt (rLet r) nG) <| andB (Nat.blt (rDep rp) (rDep r)) <|
          Nat.beq (mulK (rCode rp) (f20 G (rLet r))) c

end CFSG.KC.FiveStdK

end
