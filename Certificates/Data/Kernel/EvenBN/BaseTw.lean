module

public import Certificates.Data.Kernel.SporSch.TitsCnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def baseTw (BP nb : Nat) (gx gy gz : Nat → Nat) : Bool :=
  allN nb (fun t => strictB (pg 11 (mask 11) BP t) (fun b => Nat.beq (gx (gy b)) (gz (gx b))))

end CFSG.KS.SporSch

end
