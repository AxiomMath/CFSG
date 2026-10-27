module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.SignedWordK

open CFSG.KC.Enum (pcomp pidn)
open CFSG.KS (mask pinvS)

@[expose] noncomputable def swK (n w : Nat) (G : Nat → Nat) : List (Nat × Bool) → Nat
  | [] => pidn n w
  | l :: t => pcomp n w (mask w) (cond l.2 (G l.1) (pinvS n w (mask w) (G l.1))) (swK n w G t)

end CFSG.KC.SignedWordK

end
