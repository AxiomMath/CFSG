module

public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.BfsPinKeys
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.OrbFind

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin

@[expose] noncomputable def findK (n w : Nat) (ps : List Nat) (T S : Nat → Nat) (kv : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => S lo)
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt (pkeyK n w ps (T (S mid))) kv, ih (Nat.succ mid) hi, ih lo mid)),
      S lo))

@[expose] noncomputable def memK (n w : Nat) (ps : List Nat) (N : Nat) (T S : Nat → Nat) (v : Nat) :
    Bool :=
  strictB (findK n w ps T S (pkeyK n w ps v) (nat_lit 24) (nat_lit 0) N) fun j =>
    bAnd(Nat.blt j N, Nat.beq (T j) v)

@[expose] noncomputable def isIdK (n w P : Nat) : Bool :=
  allN n fun i => Nat.beq (pg w (mask w) P i) i

@[expose] noncomputable def isInvK (n w P : Nat) : Bool :=
  bAnd(isIdK n w (pcomp n w (mask w) P P), !isIdK n w P)

@[expose] noncomputable def ord8K (n w P : Nat) : Bool :=
  strictB (pcomp n w (mask w) P P) fun p2 => strictB (pcomp n w (mask w) p2 p2) fun p4 =>
    bAnd(isIdK n w (pcomp n w (mask w) p4 p4), !isIdK n w p4)

@[expose] noncomputable def oddK (n w P : Nat) : Bool :=
  strictB (pcomp n w (mask w) P P) fun p2 =>
    bAnd(!isIdK n w P, isIdK n w (pcomp n w (mask w) P p2) ||
      isIdK n w (pcomp n w (mask w) P (pcomp n w (mask w) p2 p2)))

@[expose] noncomputable def ord5K (n w P : Nat) : Bool :=
  strictB (pcomp n w (mask w) P P) fun p2 =>
    bAnd(!isIdK n w P, isIdK n w (pcomp n w (mask w) P (pcomp n w (mask w) p2 p2)))

end CFSG.KC.OrbFind

end
