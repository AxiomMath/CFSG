module

public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
import Certificates.Kernel.SporSch.HN.Seeds2106

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.He.Native in
theorem certificate2106 : seedChecks rowsA rowsB = true := KernelSporSch.HNSeeds.facts

end Certificates
