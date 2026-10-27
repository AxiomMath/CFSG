module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerHyperovalInputs
import Certificates.Kernel.UnitarySix.Hyperoval

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.Fischer in
theorem certificate3146 : domOK 1 = true ∧ domOK 2 = true ∧ domOK 3 = true := KernelU6.cert3146

end Certificates
