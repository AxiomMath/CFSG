module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
import Certificates.Kernel.Direct.C9320

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Hat2A7 in
theorem certificate9320 : ∀ y : A7, y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 ∨ y ^ 6 = 1 ∨
    y ^ 7 = 1 :=
  KernelDirect.C9320.a7_pow_le_seven

end Certificates
