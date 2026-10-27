module

public import Certificates.Data.Kernel.KGC31P

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum

variable (n w : Nat)

@[expose] noncomputable def pspanOK (bs : List Nat) : Bool :=
  pinSpan n w bs (pidn n w) && bs.all (pinSpan n w bs) &&
    (pspan n w bs).all fun s => pinSpan n w bs (pinv n w s) &&
      (pspan n w bs).all fun t => pinSpan n w bs (pc n w s t)

end CFSG.KC.KGC31P

end
