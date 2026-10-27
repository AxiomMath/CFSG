module

public import Certificates.Data.Kernel.U6.Tables

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def rootMaskK (nz pr : Nat → Nat) (UP c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => strictN acc fun acc => (fun v =>
      nIf(orB (Nat.beq (nz v) (nat_lit 2)) (andB (Nat.beq (nz v) (nat_lit 6)) (Nat.beq (pr v) c)),
        Nat.lor acc (pw2 p), acc)) (up UP p))
    (nat_lit 693)

@[expose] noncomputable def domK (R : Nat → Nat) (FM : Nat) : Bool :=
  allBelow (nat_lit 693) (nat_lit 11) fun q => orB (bit FM q) (strictB (R q) fun Rq =>
    anyN (nat_lit 693) fun x => andB (bit FM x) (Nat.beq (fget Rq x (nat_lit 10)) x))

@[expose] noncomputable def check3146 (nz pr : Nat → Nat) (UP : Nat) (R : Nat → Nat) (c : Nat) :
    Bool :=
  strictB (rootMaskK nz pr UP c) fun FM => domK R FM

end CFSG.KC.U6

end
