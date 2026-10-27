module

public import Certificates.Data.Kernel.LocalQT.LatM

public section

namespace CFSG.KC.LQT.L

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def validCnt (n : Nat) (U : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 1 0 (Nat.beq (getK U j) 0))) n

@[expose] noncomputable def chainInj (n : Nat) (C : List Lvl) : Bool :=
  allA C fun lv => andB (Nat.blt 0 lv.2.2.2) (Nat.beq (validCnt n lv.2.1) lv.2.2.2)

end CFSG.KC.LQT.L

end
