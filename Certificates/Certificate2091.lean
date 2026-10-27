module

public import CFSG.Sporadic.HNOddCore.SCheckInputs
import Certificates.Kernel.Sporadic.OddCore.HN2091

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native in
theorem certificate2091 : (natChainChecks = true)
    ∧ (orbitChecks = true) :=
  KernelSpor.HN2091.facts2091

end Certificates
