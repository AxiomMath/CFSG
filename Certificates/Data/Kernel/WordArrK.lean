module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.WordArr

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wordFK {k : Nat} (n w : Nat) (G : Nat → Nat) (wd : List (Fin k × Bool)) :
    Nat :=
  wd.foldl (fun A l => pcomp n w (mask w) A (if l.2 then G l.1.val else pinvS n w (mask w) (G l.1.val)))
    (pidn n w)

end CFSG.KC.WordArr

end
