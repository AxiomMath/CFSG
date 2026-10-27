module

public import Certificates.Data.Kernel.J4Q.QT2A

public section

namespace CFSG.KD.J4M4F

open CFSG.KC.J4Q

@[expose] noncomputable def fRK (c rm one : Nat) (FM : List Nat) (x : Nat) : Nat :=
  (List.range 10).foldl (fun acc j => if x.testBit j then mulJ c rm acc (getN one FM j) else acc) one

@[expose] noncomputable def fVK (rm one : Nat) (FM : List Nat) (u x : Nat) : Nat :=
  (List.range 10).foldl (fun acc j => if x.testBit j then vecJ rm acc (getN one FM j) else acc) u

@[expose] noncomputable def chkA (c rm one : Nat) (FM : List Nat) : Bool :=
  allR 10 fun i => andB (Nat.beq (mulJ c rm (getN one FM i) (getN one FM i)) one)
    (allR 10 fun j => Nat.beq (mulJ c rm (getN one FM i) (getN one FM j))
      (mulJ c rm (getN one FM j) (getN one FM i)))

@[expose] noncomputable def chkB (rm one : Nat) (FM : List Nat) (R lo n : Nat) : Bool :=
  allR n fun k => orB (Nat.beq (Nat.add lo k) 0) (neN (fVK rm one FM R (Nat.add lo k)) R)

@[expose] noncomputable def chkC (c rm one : Nat) (FM W Wi : List Nat) (CT : List (List Nat)) : Bool :=
  allR 2 fun w => allR 10 fun j =>
    Nat.beq (mulJ c rm (mulJ c rm (getN one W w) (getN one FM j)) (getN one Wi w))
      (fRK c rm one FM ((CT.getD w []).getD j 0))

@[expose] noncomputable def chkK (c rm one : Nat) (AB ABi : List Nat) (g : List Int) (R : Nat)
    (LR K : List Nat) (S : List (List Nat)) : Bool :=
  andB (Nat.beq (vecJ rm R (wordJ c rm one AB ABi g)) (K.getD 0 0))
    (andB (allR 31 fun k => Nat.blt (K.getD k 0) (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
      (allR 4 fun l => allR 31 fun k =>
        Nat.beq (vecJ rm (K.getD k 0) (getN one LR l)) (K.getD ((S.getD l []).getD k 0) 0)))

end CFSG.KD.J4M4F

end
