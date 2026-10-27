module

public import Certificates.Data.Kernel.O8.Core
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop
open CFSG.KC.Enum (pidn pcomp pg)

@[expose] noncomputable def LEVI : Nat := nat_lit 34634680249

@[expose] noncomputable def permAt (n w P s : Nat) : Nat := fget P s (Nat.mul n w)

@[expose] noncomputable def wordPermK (n w P : Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun s _ ih => pcomp n w (maskN w) (permAt n w P s) ih) ws

@[expose] noncomputable def leviOK (n w G P : Nat) (ws : List Nat) (L : Nat) : Bool :=
  andB (Nat.beq (wordRowsK G ws) L)
    (andB (allN (nat_lit 6) fun s => allN n fun i => Nat.blt (pg w (maskN w) (permAt n w P s) i) n)
      (Nat.beq (nat_lit 1) (strictN (wordPermK n w P ws) fun k => strictN (pcomp n w (maskN w) k k)
        fun k2 => nIf(Nat.beq (pcomp n w (maskN w) k2 k2) (pidn n w), nat_lit 1, nat_lit 0))))

end CFSG.KC.O8

end
