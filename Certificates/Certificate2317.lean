
module

public import Certificates.Certificate2317Base

import Certificates.Kernel.SporSch.Th.Cent
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem certificate2317 : 120754 ∈ centImageIdx := KernelSporSch.ThCent.facts2317

end Certificates
