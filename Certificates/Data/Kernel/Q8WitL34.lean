module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum (pcomp pidn)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def sqInK (n w N : Nat) (SQ : Nat → Nat) (M : Nat) (ST W : Nat → Nat) :
    Bool :=
  allN N fun i =>
    Nat.beq (SQ i) (pidn n w) || !Nat.beq (pcomp n w (mask w) (SQ i) (SQ i)) (pidn n w) ||
      (Nat.blt (W i) M && Nat.beq (ST (W i)) (SQ i))

@[expose] noncomputable def powK (n w t e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pcomp n w (mask w) t acc) e

@[expose] noncomputable def centPtK (n w : Nat) (RT : Nat → Nat) (m : Nat) (CP : Nat → Nat)
    (e k : Nat) : Bool :=
  !(allN m fun a => Nat.beq (pcomp n w (mask w) (CP a) (RT k)) (pcomp n w (mask w) (RT k) (CP a))) ||
    Nat.beq (powK n w (RT k) e) (pidn n w)

end CFSG.KC.Q8Wit

end
