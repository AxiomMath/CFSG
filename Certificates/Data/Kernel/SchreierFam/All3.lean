module

public import Certificates.Data.Kernel.SporSch.TitsEnum5

public section

namespace CFSG.KS.SchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch

@[expose] noncomputable def all3K (n w m nw : Nat) (LR TR : Nat → Nat) (Q : Nat → Bool) : Bool :=
  allN (rcnt (LR 0)) fun a => allN (rcnt (LR 1)) fun b => allN (rcnt (LR 2)) fun c =>
    Q (pcomp n w m (pcomp n w m (trAt n nw LR TR 0 a) (trAt n nw LR TR 1 b))
      (trAt n nw LR TR 2 c))

end CFSG.KS.SchreierFam
