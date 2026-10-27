module

public import Certificates.Data.Kernel.F2Word
public import Certificates.Data.Kernel.M1F2
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Tower

open CFSG.KC.F2W CFSG.KC.M1F2

@[expose] noncomputable def allL (bs : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(f c, ih)) bs

@[expose] noncomputable def nodeK (DA DB T : Nat → Nat) (j : Nat) : Bool :=
  bIf(Nat.beq (DA j) (nat_lit 2), Nat.beq (T j) (idF (nat_lit 22)),
  bIf(Nat.beq (DA j) (nat_lit 1), Nat.beq (T j) (T (nat_lit 1)),
  bIf(Nat.beq (DA j) (nat_lit 0), Nat.beq (T j) (T (nat_lit 2)),
  bIf(Nat.beq (DA j) (nat_lit 3), bAnd(Nat.blt (DB j) j,
    Nat.beq (mulW (nat_lit 22) (T (DB j)) (T j)) (idF (nat_lit 22))),
    bAnd(Nat.blt (Nat.sub (DA j) (nat_lit 4)) j, bAnd(Nat.blt (DB j) j,
      Nat.beq (T j) (mulW (nat_lit 22) (T (Nat.sub (DA j) (nat_lit 4))) (T (DB j)))))))))

@[expose] noncomputable def ptK (V W T : Nat → Nat) (off b : Nat) (bs : List Nat) (k : Nat) : Bool :=
  bAnd(Nat.blt (V (Nat.add off k)) (nat_lit 4194304),
  bAnd(Nat.blt (W (Nat.add off k)) (nat_lit 5282),
  bAnd(Nat.beq (vmF (nat_lit 22) (T (W (Nat.add off k))) b) (V (Nat.add off k)),
    allL bs fun c => Nat.beq (vmF (nat_lit 22) (T (W (Nat.add off k))) c) c)))

@[expose] noncomputable def srtK (V S : Nat → Nat) (off len m : Nat) : Bool :=
  bAnd(Nat.blt (S m) len, bIf(Nat.blt (Nat.succ m) len,
    Nat.blt (V (Nat.add off (S m))) (V (Nat.add off (S (Nat.succ m)))), true))

end CFSG.KC.Tower

end
