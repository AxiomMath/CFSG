module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.TreeK

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def normStep (v st : Nat) : Nat :=
  nIf(Nat.blt v (nat_lit 3),
    nIf(Nat.beq st (nat_lit 0),
      nIf(Nat.beq v (nat_lit 0), nat_lit 0, nIf(Nat.beq v (nat_lit 1), nat_lit 1, nat_lit 2)),
      st),
    nat_lit 2)

@[expose] noncomputable def normScan (p : Nat) (r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c st => strictN (pg (nat_lit 2) (mask (nat_lit 2)) p c) fun v => normStep v st) r

@[expose] noncomputable def ptNormK (p : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p (nat_lit 28)) (nat_lit 0),
    Nat.beq (normScan p (nat_lit 14)) (nat_lit 1))

@[expose] noncomputable def dotK (MA p r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.add acc (Nat.mul (pg (nat_lit 2) (mask (nat_lit 2)) MA
      (Nat.add (Nat.mul (nat_lit 14) r) c)) (pg (nat_lit 2) (mask (nat_lit 2)) p c)))
    (nat_lit 14)

@[expose] noncomputable def rowsK (MA p q s : Nat) : Bool :=
  allN (nat_lit 14) fun r => Nat.beq (pg (nat_lit 2) (mask (nat_lit 2)) q r)
    (Nat.mod (Nat.mul s (dotK MA p r)) (nat_lit 3))

@[expose] noncomputable def genK (G MA : Nat) (F : Nat → Nat) (i : Nat) : Bool :=
  strictB (pg (nat_lit 10) (mask (nat_lit 10)) G i) fun j =>
    bAnd(Nat.blt j (nat_lit 728),
      bIf(rowsK MA (F i) (F j) (nat_lit 1), true, rowsK MA (F i) (F j) (nat_lit 2)))

@[expose] noncomputable def ptsK (F : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 728) fun i => ptNormK (F i),
    CFSG.KC.TreeK.distinctK (nat_lit 10) ((List.range (nat_lit 728)).map F))

@[expose] noncomputable def gensK (G MA F : Nat → Nat) : Bool :=
  allN (nat_lit 4) fun k => allN (nat_lit 728) fun i => genK (G k) (MA k) F i

end CFSG.KC.G23F48

end
