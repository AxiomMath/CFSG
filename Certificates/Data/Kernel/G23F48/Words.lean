module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def evP {k : Nat} (n w : Nat) (LP LPI : Nat → Nat) :
    List (Fin k × Bool) → Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) fun l _ ih =>
    pcomp n w (mask w) (Bool.rec (motive := fun _ => Nat) (LPI l.1.val) (LP l.1.val) l.2) ih

end CFSG.KC.G23F48

end
