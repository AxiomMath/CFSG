module

public import Certificates.Data.Kernel.OrbFind

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wordK (n w : Nat) (G : Nat → Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun k _ ih => pcomp n w (mask w) (G k) ih) l

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (f i)) n

@[expose] noncomputable def fixK (n w P : Nat) : Nat :=
  cntN n fun i => Nat.beq (pg w (mask w) P i) i

@[expose] noncomputable def lettersK (ng : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.blt k ng, ih)) l

@[expose] noncomputable def bindWs (n w ng : Nat) (G0 G : Nat → Nat) (ws : List (List Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih k => bAnd(lettersK ng l, bAnd(Nat.beq (G k) (wordK n w G0 l), ih (Nat.succ k)))) ws

end CFSG.KC.A45Cls

end
