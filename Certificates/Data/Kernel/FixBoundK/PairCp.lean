module

public import Certificates.Data.Kernel.FixBoundK.Pairs

public section

namespace CFSG.KC.FixBoundK.Pair

open CFSG.KLie.CT CFSG.KC.FixBoundK

@[expose] noncomputable def cpItem (nB : Nat) (it : Item) : Bool :=
  bIf(Nat.beq it.1 (nat_lit 0), true,
    allN nB fun k => Nat.blt (fget it.2.2.1 k (nat_lit 5)) (nat_lit 24))

@[expose] noncomputable def cpAll (nB : Nat) (src : List (Nat × List Item)) : Bool :=
  allS (fun e : Nat × List Item => allS (cpItem nB) e.2) src

end CFSG.KC.FixBoundK.Pair

end
