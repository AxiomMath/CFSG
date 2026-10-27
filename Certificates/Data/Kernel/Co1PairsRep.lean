module

public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KC.Co1Pairs

open CFSG.KC.Co1B

@[expose] noncomputable def eltK (gs e : List Nat) : Nat :=
  (gs.zip e).foldl (fun acc ge => mulWK acc (powWK ge.1 ge.2)) oneK

@[expose] noncomputable def neK (X : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (eqK X oneK)

@[expose] noncomputable def threeK (X : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (neK X) (eqK (powWK X 3) oneK)

end CFSG.KC.Co1Pairs

end
