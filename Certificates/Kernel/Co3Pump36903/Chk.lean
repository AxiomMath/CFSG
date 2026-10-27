module

public import Certificates.Kernel.Co3Pump36903.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co3T.Defs
public import Certificates.Kernel.Co3T.EnumQ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Pump36903

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.Co3TK
open CertificateChecks.KernelCo3T CertificateChecks.KernelCo3Pair CertificateChecks.KernelCo3Five
open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump

theorem kSift : allN 6 (fun i => sAll (PTN.L i)) = true := by quickRfl

theorem kFuse0 : allBlk 0 fuseK 81 = true := by quickRfl

theorem kFuse1 : allBlk 81 fuseK 81 = true := by quickRfl

theorem kFuse2 : allBlk 162 fuseK 81 = true := by quickRfl

theorem kPairA : pairK 2 (DE kA) = true := by quickRfl

theorem kPairB : pairK 4 (DE kB) = true := by quickRfl

theorem kFive0 : allBlk 0 fiveK 250 = true := by quickRfl

theorem kFive1 : allBlk 250 fiveK 250 = true := by quickRfl

theorem kFive2 : allBlk 500 fiveK 250 = true := by quickRfl

theorem kFive3 : allBlk 750 fiveK 250 = true := by quickRfl

theorem kFive4 : allBlk 1000 fiveK 250 = true := by quickRfl

theorem kFive5 : allBlk 1250 fiveK 250 = true := by quickRfl

end CertificateChecks.KernelCo3Pump36903

end
