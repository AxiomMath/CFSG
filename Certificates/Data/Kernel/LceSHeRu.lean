module

public import CFSG.Certificates.Kernel.Common.LceSRange
public import CFSG.Certificates.Kernel.He.Bound.LabRange
public import CFSG.Certificates.Kernel.Ru.Bound.Lab
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.Common.Bind
public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.Certificates.LS

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def He.coneOk (blk WT RT ST LB : Nat → Nat)
    (INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (invOK INV INV8 L)
  (andB (Nat.beq nC nCa)
  (andB (Nat.ble nCa (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nCa))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq X1 (Nat.succ nf))
  (andB (HeB.hintsLt WT m (nat_lit 2) Hs)
  (andB (HeB.labsWF LB nf)
  (andB (Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (HeB.runLab WT LB Hs Cs X0) X1)))))))))))))

@[expose] noncomputable def Ru.coneOk (blk WT RT ST LB : Nat → Nat)
    (INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (invOK INV INV8 L)
  (andB (Nat.beq nC nCa)
  (andB (Nat.ble nCa (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nCa))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq X1 (Nat.succ nf))
  (andB (RuB.hintsLt WT m (nat_lit 2) Hs)
  (andB (HeB.labsWF LB nf)
  (andB (Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (RuB.runLab WT LB Hs Cs X0) X1)))))))))))))

@[expose] noncomputable def LabF.labOk (blk WT RT ST LB : Nat → Nat)
    (INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (Bind.hintsOK WT m nR nS Hs)
  (andB (LCE.relsNorm RT nR)
  (andB (invOK INV INV8 L)
  (andB (Nat.beq nC nCa)
  (andB (Nat.ble nCa (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nCa))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq X1 (Nat.succ nf))
  (andB (CFSG.KC.LabF.hintsLt WT m K Hs)
  (andB (HeB.labsWF LB nf)
  (andB (Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (CFSG.KC.LabF.runLab WT LB Hs Cs X0) X1)))))))))))))))

end CFSG.Certificates.LS

end
