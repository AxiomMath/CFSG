module

public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.KC.OpsK

open CFSG.KC.Ord CFSG.SectionRank.Native

@[expose] noncomputable def opsFpK (p w S d T L H CM RM ONE : Nat) : Ops Nat Nat where
  decode _ := 0
  mul X Y := mulR p w S d T L H CM RM X Y
  one := ONE
  eq X Y := Nat.beq X Y
  vmul v X := mulR p w S d T L H CM RM v X
  unit k := Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mul w k)) (Nat.blt k d)
  vne u v := Bool.not (Nat.beq (Nat.mod u (Nat.shiftLeft 1 S)) (Nat.mod v (Nat.shiftLeft 1 S)))

end CFSG.KC.OpsK

end
