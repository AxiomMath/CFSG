module

public import CFSG.Quasithin.H13.L32NS7ConjInputs
import Certificates.Kernel.H13.S7ConjFacts
public import Mathlib

public section

namespace Certificates

open CertificateChecks

theorem certificate7235 : CFSG.Quasithin.H13.S7Conj.s7ConjCheck = true := KernelH13.s7ConjCheck_true

end Certificates
