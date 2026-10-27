module

public import Certificates.Data.Kernel.SporSch.HNF5

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def trRow5 (T : Nat → Nat) (i : Nat) : Nat :=
  foldN (nat_lit 133) (fun j acc => Nat.lor acc
    (Nat.shiftLeft (lane5 (T j) i) (Nat.mul (nat_lit 16) j))) (nat_lit 0)

@[expose] noncomputable def fixRow5 (C : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 1), idRow5 (nat_lit 1),
    Nat.sub (C i) (Nat.shiftLeft (lane5 (C i) (nat_lit 1)) (nat_lit 16)))

@[expose] noncomputable def specRow (MT : Nat → Nat) (op l r k i : Nat) : Bool :=
  bIf(Nat.beq op (nat_lit 0), Nat.beq (vm5 (slice5 MT r) (slice5 MT l i)) (slice5 MT k i),
    bIf(Nat.beq op (nat_lit 1), Nat.beq (slice5 MT l i) (slice5 MT k i),
      bIf(Nat.beq op (nat_lit 2), true, Nat.beq (trRow5 (slice5 MT l) i) (slice5 MT k i))))

@[expose] noncomputable def entryOK2 (MT OP L R : Nat → Nat) (k b : Nat) : Bool :=
  strictB (OP k) (fun op => strictB (L k) (fun l => strictB (R k) (fun r =>
    allBlk (Nat.mul (nat_lit 19) b) (fun i => specRow MT op l r k i) (nat_lit 19))))

@[expose] noncomputable def recRow5 (MT : Nat → Nat) (kV kA kB : Nat) (recs : List (Nat × Nat))
    (i : Nat) : Bool :=
  strictB (recs.getD i (nat_lit 0, nat_lit 0)).1 (fun j => strictB (recs.getD i (nat_lit 0, nat_lit 0)).2
    (fun l => bAnd(Nat.blt j i, bAnd(bIf(Nat.beq l (nat_lit 1), true, Nat.beq l (nat_lit 2)),
      Nat.beq (vm5 (slice5 MT (nIf(Nat.beq l (nat_lit 1), kA, kB))) (slice5 MT kV j))
        (slice5 MT kV i)))))

end CFSG.KS.SporSch

end
