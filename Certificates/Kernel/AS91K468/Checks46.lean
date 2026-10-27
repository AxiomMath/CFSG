module

public import Certificates.Data.Kernel.AS91K468.K46
public import Certificates.Kernel.AS91K468.Data46
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K468

open Certificates.Kernel.AS91K468 Certificates.Kernel.HJ12K CFSG.KC.Mat12P

theorem ch89406_words : wordsOK46 = true := by quickRfl

theorem ch89406_w1 : w1OK46Q = true := by quickRfl

theorem ch89406_eb : eb46Q = true := by quickRfl

theorem ch89406_trans : trans46Q = true := by quickRfl

theorem ch89406_pnodup : pNodup46Q = true := by quickRfl

theorem ch89406_pf : (pfOf (enumQ pQ) == CFSG.KD.AS91K46.pfL) = true := by quickRfl

end CertificateChecks.KernelAS91K468
