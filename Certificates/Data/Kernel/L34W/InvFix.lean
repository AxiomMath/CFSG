module

public import Certificates.Data.Kernel.L34W.ModK

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K

@[expose] noncomputable def cf22Lab (T A Y : Nat → Nat) (t i x : Nat) : Bool :=
  bAnd(bNot (Nat.beq (Y (Nat.div x (nat_lit 16))) (pidn (nat_lit 42) (nat_lit 6))),
    bAnd(eqC (nat_lit 1) (mulC T x x) (nat_lit 0), eqC (nat_lit 1) (betaC T A t i x) x))

@[expose] noncomputable def cf22Any (T A Y : Nat → Nat) (t i : Nat) (m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun x ih => bIf(cf22Lab T A Y t i x, true, ih)) m

@[expose] noncomputable def cf22One (T A Y : Nat → Nat) (n : Nat) : Bool :=
  bIf(invPt (nat_lit 42) (nat_lit 6) (Y n),
    cf22Any T A Y (Nat.mod n (nat_lit 64)) (Nat.div n (nat_lit 64)) (nat_lit 1024), true)

@[expose] noncomputable def cf22K (T A Y : Nat → Nat) : Bool :=
  allN (nat_lit 2304) fun n => cf22One T A Y n

end CFSG.KC.L34W

end
