module

public import Certificates.Kernel.Co1B.Dag25170
public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Data.Kernel.SporSch.Co1MatW
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoBInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Comm25170

open CFSG.KS.SporSch.M24 CFSG.KC.Co1B CertificateChecks.KernelCo1B

theorem kCD : dagWK CD.M CD.MI 4 6 CD.KW = true := by quickRfl

theorem kCB : (Nat.beq (CD.M 0) (Syl2B.S2.M 80) && Nat.beq (CD.M 1) (Syl2B.S2.M 81) &&
    Nat.beq (CD.M 2) (Syl2B.S2.M 82) && Nat.beq (CD.M 3) (Syl2B.S2.M 83)) = true := by quickRfl

theorem kCW : CD.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    [CFSG.EvenSporadicStandard.Solomon78.twoBCommWX,
      CFSG.EvenSporadicStandard.Solomon78.twoBCommWY] := by decide +kernel

theorem kComm : (Nat.beq (mulWK (CD.M 4) (Cent2045.D1.M 0)) (mulWK (Cent2045.D1.M 0) (CD.M 4)) &&
    Nat.beq (mulWK (CD.M 5) (Cent2045.D1.M 0)) (mulWK (Cent2045.D1.M 0) (CD.M 5)) &&
    Nat.beq (mulWK (CD.M 4) (CD.M 5))
      (mulWK (Cent2045.D1.M 0) (mulWK (CD.M 5) (CD.M 4)))) = true := by quickRfl

end CertificateChecks.KernelCo1B.Comm25170

end
