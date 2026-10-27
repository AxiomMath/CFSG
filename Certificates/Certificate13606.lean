module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONWitnessInputs
import Certificates.Kernel.Sporadic.ONW.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate13606 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native.onWitnessChecks () = true :=
  KernelSpor.ONW.onWitnessChecks_true

end Certificates
