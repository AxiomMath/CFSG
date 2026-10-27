
module


public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import Certificates.Kernel.UnitarySix.LettersBase

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix in
theorem certificate3180 : ∀ k < 46, involOK (letterT k) = true := KernelU6.cert3180

end Certificates
