module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.F2Set24

public section

namespace CFSG.KC.Co1Pairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KC.Co1B

@[expose] noncomputable def neOne (X : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (Nat.beq X idM)

@[expose] noncomputable def eltOK (M MI : Nat → Nat) (w : List Nat) (X R q : Nat) : Bool :=
  bAnd(lettersK (nat_lit 75) w, bAnd(Nat.beq (wordWK M MI w) X,
    bAnd(Nat.beq (mulWK X R) (mulWK R X), bAnd(Nat.beq (powWK X q) idM, neOne X))))

@[expose] noncomputable def prodOK (X Y d : Nat) : Bool :=
  CFSG.KC.F2Set24.strict (mulWK X Y) fun Z => bAnd(Nat.beq (powWK Z d) idM, neOne Z)

end CFSG.KC.Co1Pairs

end
