module

public import Certificates.Data.Kernel.Misc.BfsK

public section

namespace CFSG.KD.YamakiGenPos

open CFSG.KD.BfsK

@[expose] noncomputable def genPosK (R : Nat → Nat) (o n : Nat) : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: is, p :: ps => Nat.blt p n && Nat.beq (recX R o p) (R i) && genPosK R o n is ps

end CFSG.KD.YamakiGenPos

end
