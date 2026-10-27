module

public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Kernel.Co1B.Bfs24513
public import Certificates.Data.Kernel.SporSch.Co1Cent
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.SporSch.Co1Mat
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public import CFSG.Sporadic.Co1Block.TwoBData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

theorem kBindS : bindK Cent2045.D1.M S2.M twoBBray = true := by quickRfl
theorem kS2 : dagIK S2.M S2.MI twoBBray.length S2.N sylD2B = true := by quickRfl
theorem kN : (Nat.beq ST.N 32768 && sylIdxB.all (fun j => decide (j < S2.N))) = true := by
  quickRfl
theorem kInvB : allN twoBBray.length (fun i => invOKK (S2.M i) (S2.MI i)) = true := by quickRfl

end CertificateChecks.KernelCo1B.Syl2B

end
