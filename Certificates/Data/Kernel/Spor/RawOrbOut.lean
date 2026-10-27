module

public import Certificates.Data.Kernel.Spor.RawOrb

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def outK (n w m nw idn : Nat) (S SI : Nat → Nat) (kS BP l R : Nat)
    (iw : List Int) (X : Nat) : Bool :=
  bAnd(lettersK kS iw, strictB (pcomp n w m (wordK n w m idn S SI iw) X) (fun q =>
    bAnd(allN l (fun t => strictB (pg w m BP t) (fun b => Nat.beq (pg w m q b) b)),
      strictB (pg w m BP l) (fun b => Nat.ble (rcnt R) (rpos w m nw R (pg w m q b))))))

end CFSG.KS.Raw

end
