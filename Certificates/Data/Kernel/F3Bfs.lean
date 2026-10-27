module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.F3Bfs

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bfsHit (fp fl : Nat → Nat) (h l x n : Nat) : Nat :=
  nIf(Nat.beq n (nat_lit 0), nat_lit 0, nIf(Nat.blt x n, n,
    nIf(Nat.beq x n, nIf(Nat.beq (fp n) h, nIf(Nat.beq (fl n) l, Nat.succ n, nat_lit 0),
      nat_lit 0), nat_lit 0)))

@[expose] noncomputable def bfsStep (fa fb fp fl : Nat → Nat) (h n : Nat) : Nat :=
  nIf(Nat.blt h n,
    strictN (bfsHit fp fl h (nat_lit 1) (fa h) n) (bfsHit fp fl h (nat_lit 2) (fb h)), nat_lit 0)

@[expose] noncomputable def bfsOrderOK (fa fb fp fl : Nat → Nat) (N : Nat) : Bool :=
  bAnd(Nat.beq (fp (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (fl (nat_lit 0)) (nat_lit 0),
    Nat.beq (foldUp N (bfsStep fa fb fp fl) (nat_lit 1)) N))

end CFSG.KC.F3Bfs
