module

public import Certificates.Data.Kernel.E8Plane.Check

public section

namespace CFSG.KC.E8Plane

open CFSG.KC.E7Plane

@[expose] noncomputable def sortB (RP SP IP : Nat) : Bool :=
  andB (allN 239 fun k => Nat.blt (fld SP 32 k) (fld SP 32 (Nat.succ k)))
    (allN 240 fun k => andB (Nat.blt (fld IP 8 k) 240)
      (Nat.beq (fld RP 32 (fld IP 8 k)) (fld SP 32 k)))

@[expose] noncomputable def lettB (CJ : List (Nat × Nat × List Nat)) : Bool :=
  allL CJ fun x => allL x.2.2 fun i => Nat.blt i 8

end CFSG.KC.E8Plane
