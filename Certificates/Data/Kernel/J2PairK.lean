module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.J2PairK

open CFSG.KS CFSG.KS.Prim CFSG.KC.Enum

@[expose] noncomputable def pw (PS : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (pidn 315 9) (fun i _ acc => pcomp 315 9 (mask 9) (PS i) acc) w

@[expose] noncomputable def pairK (R U V : Nat) : Bool :=
  Nat.beq (pcomp 315 9 (mask 9) U R) (pcomp 315 9 (mask 9) R U) &&
    Nat.beq (pcomp 315 9 (mask 9) V R) (pcomp 315 9 (mask 9) R V) &&
    Nat.beq (pcomp 315 9 (mask 9) U U) (pidn 315 9) &&
    Nat.beq (pcomp 315 9 (mask 9) V V) (pidn 315 9) && !Nat.beq U (pidn 315 9) &&
    !Nat.beq V (pidn 315 9) && !Nat.beq U V &&
    Nat.beq (pcomp 315 9 (mask 9) U V) (pcomp 315 9 (mask 9) V U)

end CFSG.KC.J2PairK
