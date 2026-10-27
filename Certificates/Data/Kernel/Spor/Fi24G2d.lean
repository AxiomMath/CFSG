module

public import Certificates.Data.Kernel.Spor.Fi24Orb

public section

namespace CFSG.KC.Fi24G2d

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24Orb

@[expose] noncomputable def idN (i : Nat) : Nat := i

@[expose] noncomputable def listStep (FL : Nat → Nat) (TG : Nat → Nat → Nat) (u : List Nat)
    (n m j : Nat) : Bool :=
  letB (FL j) (fun r => andB (Nat.blt r n) (andB (Nat.beq (walk TG u r) r)
    (orB (Nat.ble m (Nat.succ j)) (Nat.blt r (FL (Nat.succ j))))))

@[expose] noncomputable def fixLOK (FL : Nat → Nat) (TG : Nat → Nat → Nat) (u : List Nat)
    (n m : Nat) : Bool :=
  allBelow m (nat_lit 16) (fun j => listStep FL TG u n m j)

end CFSG.KC.Fi24G2d

end
