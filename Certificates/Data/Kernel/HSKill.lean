module

public import Certificates.Data.Kernel.HOrb
public import CFSG.Certificates.Kernel.Common.LceSRange
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Lab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Pair

public section

namespace CFSG.Certificates.HSKill

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.Certificates.HO

@[expose] noncomputable def coneOk (blk WT RT ST LB LETs : Nat → Nat)
    (INV INV8 L nC nf m Hs K S0 S1 T0 T1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (invOK INV INV8 L)
  (andB (Nat.ble nC (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nC))
  (andB (Nat.beq T0 (nat_lit 1))
  (andB (Nat.beq T1 (Nat.succ nf))
  (andB (CFSG.KC.HSK.hintsLt WT m K Hs)
  (andB (Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (CFSG.KC.HSK.runLab WT LB LETs Hs Cs T0) T1)))))))))))

@[expose] noncomputable def gwOK (GW : Nat → Nat) (ng : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
    (andB (CFSG.KC.HSK.conjOK (GW (Nat.succ k))) (entOK (GW (Nat.succ k)) (nat_lit 4) (nat_lit 63)))) ng

@[expose] noncomputable def pairArgsOK (ng w hn m : Nat) : Bool :=
  andB (entOK w (Nat.mul (nat_lit 2) ng) (nat_lit 8))
    (andB (Nat.ble hn (nat_lit 32))
      (Nat.blt (Nat.mul (Nat.add (Nat.mul (nat_lit 2) (wLen w)) (nat_lit 2)) m) (nat_lit 1024)))

end CFSG.Certificates.HSKill

end
