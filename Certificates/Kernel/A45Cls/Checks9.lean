module

public import Certificates.Kernel.A45Cls.Grp
public import Certificates.Kernel.A45Cls.Data6
public import Certificates.Data.Kernel.A45Cls.E16Walk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.E16Walk

theorem ce16inv : invOK SY.T SY.N CFSG.KD.E16W.invMask = true := by quickRfl

theorem ce16tab : tabOK CFSG.KD.E16W.invMask 43 CFSG.KD.E16W.posT CFSG.KD.E16W.jT
    CFSG.KD.E16W.invE = true := by quickRfl

theorem ce16full : Nat.beq CFSG.KD.E16W.full (Nat.sub (Nat.shiftLeft 1 43) 1) = true := by quickRfl

theorem ce16pos : posOK SY.N CFSG.KD.E16W.invMask CFSG.KD.E16W.posT CFSG.KD.E16W.jT = true := by
  quickRfl

theorem ce16adj : adjOK SY.T CFSG.KD.E16W.invE = true := by quickRfl

theorem ce16nodes2 : nodesOK ps SY.T SY.S SY.N CFSG.KD.E16W.posT CFSG.KD.E16W.jT
    CFSG.KD.E16W.invE CFSG.KD.E16W.L2 = true := by quickRfl

theorem ce16nodes3 : nodesOK ps SY.T SY.S SY.N CFSG.KD.E16W.posT CFSG.KD.E16W.jT
    CFSG.KD.E16W.invE CFSG.KD.E16W.L3 = true := by quickRfl

theorem ce16nodes4 : nodesOK ps SY.T SY.S SY.N CFSG.KD.E16W.posT CFSG.KD.E16W.jT
    CFSG.KD.E16W.invE CFSG.KD.E16W.L4 = true := by quickRfl

theorem ce16par2 : par1OK CFSG.KD.E16W.full CFSG.KD.E16W.L2 = true := by quickRfl

theorem ce16par3 : parOK CFSG.KD.E16W.full CFSG.KD.E16W.L2 CFSG.KD.E16W.L3 = true := by quickRfl

theorem ce16par4 : parOK CFSG.KD.E16W.full CFSG.KD.E16W.L3 CFSG.KD.E16W.L4 = true := by quickRfl

theorem ce16compl1 : compl1K CFSG.KD.E16W.full CFSG.KD.E16W.invE CFSG.KD.E16W.L2 = true := by
  quickRfl

theorem ce16compl2 : complK CFSG.KD.E16W.full CFSG.KD.E16W.invE CFSG.KD.E16W.L2
    CFSG.KD.E16W.L3 = true := by quickRfl

theorem ce16compl3 : complK CFSG.KD.E16W.full CFSG.KD.E16W.invE CFSG.KD.E16W.L3
    CFSG.KD.E16W.L4 = true := by quickRfl

theorem ce16fix : fixOK SY.T CFSG.KD.E16W.fix15 CFSG.KD.E16W.fixP CFSG.KD.E16W.invE = true := by
  quickRfl

theorem ce16good : goodK CFSG.KD.E16W.fix15 CFSG.KD.E16W.fixP CFSG.KD.E16W.L4 = true := by
  quickRfl

end CertificateChecks.KernelA45
