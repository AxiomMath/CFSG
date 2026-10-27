module

public import Certificates.Data.Kernel.Co1T13K
public import Certificates.Data.CFSGNative.Solomon.Co1T13
public import Certificates.Kernel.Co1T13K.Data
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.SporSch.Co1.Packed
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1T13K

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1T13K CFSG.KS.SporSch.M24
  CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelCo1B.Bound17591 (XB)

theorem ch13504base : (Nat.beq (getL 0 CFSG.KD.Co1T13K.M 0) PA &&
    Nat.beq (getL 0 CFSG.KD.Co1T13K.M 1) PB) = true := by quickRfl

theorem ch13504dag : dagWK (getL 0 CFSG.KD.Co1T13K.M) (getL 0 CFSG.KD.Co1T13K.MI) 2 4
    Solomon.Co1T13.dagWords13 = true := by quickRfl

theorem ch13504yt : (Nat.beq CFSG.KD.Co1T13K.YT.length 13 &&
    allN 13 (fun t => Nat.beq (getL 0 CFSG.KD.Co1T13K.YT t)
      (trK 24 (powWK (getL 0 CFSG.KD.Co1T13K.M 3) t))) &&
    Nat.beq (powWK (getL 0 CFSG.KD.Co1T13K.M 3) 13) idM &&
    !Nat.beq (getL 0 CFSG.KD.Co1T13K.M 3) idM) = true := by quickRfl

theorem ch13504set0 : (Nat.beq CFSG.KD.Co1T13K.R0.length 12 &&
    setOK XB CFSG.KD.Co1T13K.YT 139 131 CFSG.KD.Co1T13K.R0) = true := by quickRfl

theorem ch13504set1 : (Nat.beq CFSG.KD.Co1T13K.R1.length 12 &&
    setOK XB CFSG.KD.Co1T13K.YT 157 455 CFSG.KD.Co1T13K.R1) = true := by quickRfl

end CertificateChecks.KernelCo1T13K

end
