module

public import Certificates.Data.Kernel.Hall82K.Rm

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT

@[expose] noncomputable def cntK (p : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.add ih (Bool.rec 0 1 (p i))) n

@[expose] noncomputable def fixMK (R m v : Nat) : Bool :=
  P.allN 8 fun e => P.impB (inM m e) (Nat.beq (apL (rmC R e) v) v)

@[expose] noncomputable def le32K (R m : Nat) : Bool :=
  P.impB (andB (closed8K m) (negK (Nat.beq m 1)))
    (Nat.ble (Nat.mul (cntK (inM m) 8) (cntK (fixMK R m) 64)) 32)

end CFSG.KC.Hall82K
