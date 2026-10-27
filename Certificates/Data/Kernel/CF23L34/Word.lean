module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.CF23L34

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ltrK (G GI : Nat → Nat) (l : Fin 2 × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2

@[expose] noncomputable def evK (n w : Nat) (G GI : Nat → Nat) (x : List (Fin 2 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun l _ ih => strictN ih (fun r => pcomp n w (mask w) (ltrK G GI l) r)) x

end CFSG.KC.CF23L34

end
