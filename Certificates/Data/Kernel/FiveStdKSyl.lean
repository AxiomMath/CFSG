module

public import Certificates.Data.Kernel.FiveStdKOrb

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def powK (x n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) oneK (fun _ ih => mulK ih x) n

@[expose] noncomputable def f16 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul i 16)) 65535

@[expose] noncomputable def sylPt (OR OM : List Nat) (nR x y p W t : Nat) : Bool :=
  letB (f16 W t) fun w => letB (Nat.div w 4096) fun k => letB (Nat.mod w 4096) fun j =>
    andB (Nat.blt k nR) <| andB (Nat.blt j (OM.getD k 0)) <|
      Nat.beq (oCode (f96 (OR.getD k 0) j))
        (mulK (powK x (Nat.div (Nat.succ t) p)) (powK y (Nat.mod (Nat.succ t) p)))

@[expose] noncomputable def sylOK (OR OM : List Nat) (nR x y p W : Nat) : Bool :=
  andB (validK x) <| andB (validK y) <| andB (Nat.beq (mulK x y) (mulK y x)) <|
  andB (Nat.beq (powK x p) oneK) <| andB (Nat.beq (powK y p) oneK) <|
  andB (!Nat.beq x oneK) <| andB (!Nat.beq y oneK) <|
    allN (Nat.sub (Nat.mul p p) 1) (sylPt OR OM nR x y p W)

end CFSG.KC.FiveStdK

end
