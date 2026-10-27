module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.M12Dec

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def b64K (c : Nat) : Nat :=
  nIf(Nat.beq c 43, 62, nIf(Nat.beq c 47, 63, nIf(Nat.ble c 57, Nat.sub c 48,
    nIf(Nat.ble c 90, Nat.sub c 55, Nat.sub c 61))))

@[expose] noncomputable def rowsOf (w P q : Nat) : Nat := pg (Nat.mul 64 w) (mask (Nat.mul 64 w)) P q

@[expose] noncomputable def strB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def decK (k w : Nat) (R : Nat → Nat) (N : Nat) (cs : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ idx => Nat.beq idx N)
    (fun c _ ih cnt cur idx =>
      (fun v => bIf(Nat.beq (Nat.succ cnt) k,
        bAnd(strB (Nat.div idx 64) (fun q => Nat.beq (pg w (mask w) (R q) (Nat.mod idx 64)) v),
          strB (Nat.succ idx) (ih 0 0)),
        ih (Nat.succ cnt) v idx)) (Nat.add (Nat.mul cur 64) (b64K c.toNat))) cs

end CFSG.KC.M12Dec

end
