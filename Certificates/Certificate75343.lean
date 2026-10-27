module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuzInputs
public meta import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuzInputs
import Certificates.Kernel.Sporadic.OddCore.SuzPairF

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.WeakClosure81.SporSuz in
theorem certificate75343 : suzPairOK () = true :=
  KernelSpor.SuzPair.pair_true

end Certificates

end
