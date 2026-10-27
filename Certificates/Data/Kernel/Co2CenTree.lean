module

public import Certificates.Data.Kernel.Co2J

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2J CFSG.KC.M1F2 CFSG.KLie.CT

@[expose] noncomputable def edgeN (PE : Nat → Nat) (N m X g t : Nat) : Bool :=
  implK (notK (Nat.blt t m)) (andK (Nat.blt t N) (Nat.beq (PE t) (mulT X g)))

@[expose] noncomputable def nextN (PM : Nat → Nat) (N s : Nat) : Nat :=
  selN (Nat.blt (Nat.succ s) N) (PM (Nat.succ s)) N

@[expose] noncomputable def sortN (PE PS : Nat → Nat) (N s : Nat) : Bool :=
  andK (Nat.blt (PS s) N) (implK (Nat.blt (Nat.succ s) N)
    (Nat.blt (PE (PS s)) (PE (PS (Nat.succ s)))))

@[expose] noncomputable def recN (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat)
    (N s : Nat) : Bool :=
  letB (PE s) fun X => letB (PM s) fun m =>
    andK (edgeN PE N m X (MK (nat_lit 0)) (PT s (nat_lit 0))) (
    andK (edgeN PE N m X (MK (nat_lit 1)) (PT s (nat_lit 1))) (
    andK (edgeN PE N m X (MK (nat_lit 2)) (PT s (nat_lit 2))) (
    andK (edgeN PE N m X (MK (nat_lit 3)) (PT s (nat_lit 3))) (
    andK (edgeN PE N m X (MK (nat_lit 4)) (PT s (nat_lit 4))) (
    andK (Nat.blt s m) (andK (Nat.ble m N) (
    andK (Nat.beq (rowK m (PT s (nat_lit 0)) (PT s (nat_lit 1)) (PT s (nat_lit 2))
        (PT s (nat_lit 3)) (PT s (nat_lit 4))) (nextN PM N s))
      (sortN PE PS N s))))))))

@[expose] noncomputable def treeNK (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat)
    (N : Nat) : Bool :=
  andK (Nat.blt N BAD) (andK (Nat.beq (PE (nat_lit 0)) IDT) (andK (Nat.beq (PM (nat_lit 0))
    (nat_lit 1)) (allK N (recN PE PM PS PT MK N))))

end CFSG.KC.Co2Cen

end
