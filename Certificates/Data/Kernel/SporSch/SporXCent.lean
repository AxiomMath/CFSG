module

public import Certificates.Data.Kernel.SporSch.SporXElem

public section

namespace CFSG.KS.SporXE

open CFSG.KC.Enum CFSG.KS.SporSch

@[expose] noncomputable def cmB (bs : List Nat) (t : Nat → Nat) (fs : List (Nat → Nat)) : Bool :=
  allF (fun f => eqOnL bs (fun x => f (t x)) (fun x => t (f x))) fs

end CFSG.KS.SporXE

end
