module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs

public section

namespace CertificateChecks.KernelDirect.C9320

open CFSG.ClassicalInvolution.Hat2A7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem a7_pow_le_seven :
    ∀ y : A7, y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 ∨ y ^ 6 = 1 ∨
      y ^ 7 = 1 := by
  decide +kernel

end CertificateChecks.KernelDirect.C9320
