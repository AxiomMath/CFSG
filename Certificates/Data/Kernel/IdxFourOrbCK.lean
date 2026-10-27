module

public import Certificates.Data.Kernel.IdxFourReachK

public section

namespace CFSG.KC.IF4V

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.KC.IF4L CFSG.KC.IF4W

@[expose] noncomputable def o1701K (n : Nat) : Bool :=
  Nat.beq (wtK n) 4 || (Nat.beq (wtK n) 6 && !Nat.beq (peK n) 0)

@[expose] noncomputable def inCK (n : Nat) : Bool := o1701K n && !f0K n 3

@[expose] noncomputable def labK (L n : Nat) : Nat := Nat.land (Nat.shiftRight L (Nat.mul 2 n)) 3

@[expose] noncomputable def predK (L i n : Nat) : Bool := inCK n && Nat.beq (labK L n) i

@[expose] noncomputable def cntBelow (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => bif f k then Nat.succ ih else ih) n

@[expose] noncomputable def repK (i : Nat) : Nat := fld 14228354355215 i

@[expose] noncomputable def orbCi (G D L i : Nat) : Bool :=
  reachOK G D (repK i) 2 (predK L i) && Nat.ble 64 (cntBelow 4096 (predK L i))

@[expose] noncomputable def orbCOK (G D L : Nat) : Bool := allBelow 4 (orbCi G D L)

end CFSG.KC.IF4V

end
