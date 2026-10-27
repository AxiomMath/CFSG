module

public import Certificates.Data.Kernel.SuzNine.Defs

public section

namespace CFSG.KC.SuzNine

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def listKey (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.add p (Nat.shiftLeft ih (nat_lit 11))) L

@[expose] noncomputable def belowK (c k g v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (Nat.blt (fldK g (fldK k j)) v)) c

@[expose] noncomputable def setK (c k g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (fldK g (fldK k i))
      (Nat.mul (nat_lit 11) (belowK c k g (fldK g (fldK k i)))))) c

@[expose] noncomputable def movedAt (c : Nat) (E UG : Nat → Nat) (k : Nat) : Bool :=
  impB (Nat.blt (nat_lit 0) k)
    (notB (allN (nat_lit 4) fun j => Nat.beq (setK c (E k) (UG j)) (E k)))

@[expose] def XW : List Int := [7, 10]

@[expose] def YW : List Int := [9, 7, 10, 9]

@[expose] def AW : List Int := [5, 2, 6, 5, 2, 6]

@[expose] def GW : List Int := [8, 4, 2]

@[expose] def X0L : List Nat := [818, 827, 1095, 1187, 1637, 1754]

@[expose] def X3L : List Nat := [1095, 1187, 1637, 1754]

end CFSG.KC.SuzNine

end
