module

public import Certificates.Data.Kernel.Fi23Q.Chain

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum

@[expose] noncomputable def fixG (img : Nat → Nat → Nat) (p : Nat) (R : List (Nat × List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(allL l.2 fun v => Nat.beq (img v p) p, ih)) R

@[expose] noncomputable def chainG (img : Nat → Nat → Nat) (ok : Nat → Bool)
    (Ls : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l R ih => bAnd(Nat.blt l.1 (nat_lit 31671), bAnd(allL l.2 ok,
      bAnd(nodupN (l.2.map fun v => img v l.1), bAnd(fixG img l.1 R, ih))))) Ls

end CFSG.KC.Fi23Q

end
