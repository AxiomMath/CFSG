module

public import Certificates.Data.Kernel.D4LocalK

public section

namespace CFSG.KC.D4Local

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

@[expose] noncomputable def wordPos {m : Nat} (n w : Nat) (G : Nat → Nat) (ws : List (Fin m × Bool)) :
    Nat :=
  List.rec (pidn n w) (fun x _ r => pcomp n w (mask w) (G x.1.val) r) ws

end CFSG.KC.D4Local
