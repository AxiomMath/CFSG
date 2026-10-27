module

public import Certificates.Kernel.B3S3.Gen
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo3T.E

public meta def qG : Array (Array Nat) :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.qGens ()

end CertificateChecks.KernelCo3T.E

public section

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelCo3T.EQ CertificateChecks.KernelCo3T.E.qG
  CFSG.Sporadic.Schreier.Co3.co3ChainBaseArr 276 9

end
