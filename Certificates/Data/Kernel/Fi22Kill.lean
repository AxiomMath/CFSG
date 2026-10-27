module

public import Certificates.Data.Kernel.HOrb
public import CFSG.Certificates.Kernel.Common.LceSRange
public import CFSG.Certificates.Kernel.Fi22.Bound2.Lab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Pair

public section

namespace CFSG.Certificates.Fi22Kill

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
  (andB (CFSG.KC.Fi22K.hintsLt WT m K Hs)
  (andB (Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (CFSG.KC.Fi22K.runLab WT LB LETs Hs Cs T0) T1)))))))))))

@[expose] noncomputable def wf4 (X : Nat) : Bool := Nat.blt X (Nat.shiftLeft (nat_lit 1) (nat_lit 1458))

@[expose] noncomputable def eShape (g : Nat) : Bool :=
  andB (entOK (CFSG.KC.Fi22K.eAB g) (nat_lit 4) (nat_lit 31))
    (andB (Nat.beq (Nat.land (wLen (CFSG.KC.Fi22K.eAB g)) (nat_lit 1)) (nat_lit 1))
      (andB (Nat.beq (wLet (wWord (CFSG.KC.Fi22K.eAB g)) (CFSG.KC.Fi22K.eHalf g)) (nat_lit 0))
        (Nat.beq (CFSG.KC.Fi22K.sigma g) (invEnt (CFSG.KC.Fi22K.sigInv g)))))

@[expose] noncomputable def eOK : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (eShape (Nat.succ k))) (nat_lit 6)

@[expose] noncomputable def pairArgsOK (i j w hn : Nat) : Bool :=
  andB (Nat.ble (nat_lit 1) i) (andB (Nat.ble i (nat_lit 6))
    (andB (Nat.ble (nat_lit 1) j) (andB (Nat.ble j (nat_lit 6))
      (andB (entOK w (nat_lit 12) (nat_lit 16)) (Nat.ble hn (nat_lit 32))))))

end CFSG.Certificates.Fi22Kill

end
