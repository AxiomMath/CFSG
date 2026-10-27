module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.G24Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def ordAuxK (t d : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun p => Nat.beq p (pidn 1365 11))
    (fun _ ih p => neIdK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) p &&
      ih (pcomp 1365 11 (mask 11) t p)) d

end CFSG.KC.G24Tri

end
