module

public import Certificates.Data.Kernel.Co2Kill

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS

theorem lceOk_intro {blk WT RT ST LVs : Nat → Nat}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : Nat} {Cs CCs : List Nat} {S0 S1 X0 X1 : Nat}
    (h1 : invOK INV INV8 L = true) (h2 : wordsOK WT RT ST INV INV8 m Hs = true)
    (h3 : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true) (h4 : aliveOK LVs mLV nCl a = true)
    (h5 : Nat.beq nC nCl = true) (h6 : Nat.ble nC (nat_lit 1048576) = true)
    (h6' : Nat.blt nf (nat_lit 4294967296) = true)
    (h7 : Nat.blt (nat_lit 0) m = true) (h8 : CFSG.Certificates.LCE.wtPer WT m = true)
    (h9 : CFSG.Certificates.LCE.relsNorm RT nR = true)
    (h10 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true)
    (h11 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h12 : Nat.beq S1 (mkS nf nC) = true) (h13 : Nat.beq X0 (nat_lit 1) = true)
    (h14 : Nat.beq (runCover blk LVs nf L CCs X0) X1 = true) (h15 : Nat.beq X1 (Nat.succ nC) = true) :
    CFSG.Certificates.LCE.lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs S0 S1 X0 X1 =
      true := by
  unfold CFSG.Certificates.LCE.lceOk
  rw [h1, h2, h3, h4, h5, h6, h6', h7, h8, h9, h10, h11, h12, h13, h14, h15]
  rfl

theorem factsOk_intro {blk WT RT ST : Nat → Nat} {INV INV8 L nC m Hs nR nS nf S0 S1 : Nat}
    {Cs : List Nat}
    (h1 : invOK INV INV8 L = true) (h2 : wordsOK WT RT ST INV INV8 m Hs = true)
    (h3 : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true) (h4 : Nat.blt (nat_lit 0) m = true)
    (h5 : CFSG.Certificates.LCE.wtPer WT m = true) (h6 : CFSG.Certificates.LCE.relsNorm RT nR = true)
    (h7 : Nat.ble nC (nat_lit 1048576) = true) (h8 : Nat.blt nf (nat_lit 4294967296) = true)
    (h9 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h10 : Nat.beq S1 (mkS nf nC) = true)
    (h11 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true) :
    CFSG.Certificates.HO.factsOk blk WT RT ST INV INV8 L nC m Hs nR nS nf S0 S1 Cs = true := by
  unfold CFSG.Certificates.HO.factsOk
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  rfl

theorem coneOk_intro {blk WT RT ST LB LETs : Nat → Nat}
    {INV INV8 L nC nf m Hs K S0 S1 T0 T1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.ble nC (nat_lit 1048576) = true) (h4 : Nat.blt nf (nat_lit 4294967296) = true)
    (h5 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h6 : Nat.beq S1 (mkS nf nC) = true)
    (h7 : Nat.beq T0 (nat_lit 1) = true) (h8 : Nat.beq T1 (Nat.succ nf) = true)
    (h9 : CFSG.KC.Co2K.hintsLt WT m K Hs = true)
    (h10 : Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h11 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h12 : Nat.beq (CFSG.KC.Co2K.runLab WT LB LETs Hs Cs T0) T1 = true) :
    CFSG.Certificates.Co2Kill.coneOk blk WT RT ST LB LETs INV INV8 L nC nf m Hs K S0 S1 T0 T1 Cs =
      true := by
  unfold CFSG.Certificates.Co2Kill.coneOk
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  rfl

end CertificateChecks.KernelCo2

end
