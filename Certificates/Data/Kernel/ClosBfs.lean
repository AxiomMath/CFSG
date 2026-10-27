module

public import Certificates.Data.Kernel.F3Bfs

public section

namespace CFSG.KC.ClosBfs

open CFSG.KC.Enum CFSG.KS CFSG.KC.F3Bfs

@[expose] noncomputable def closRow (gs : Nat) (fn fp fl : Nat → Nat) (h c : Nat) : Nat :=
  nIf(Nat.blt h c, foldUp gs (fun k s => bfsHit fp fl h k (fn (Nat.add (Nat.mul h gs) k)) s) c,
    nat_lit 0)

@[expose] noncomputable def closBfsOK (gs : Nat) (fn fp fl : Nat → Nat) (N : Nat) : Bool :=
  bAnd(Nat.beq (fp (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (fl (nat_lit 0)) (nat_lit 0),
    Nat.beq (foldUp N (closRow gs fn fp fl) (nat_lit 1)) N))

end CFSG.KC.ClosBfs

end
