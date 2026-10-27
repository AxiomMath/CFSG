module

public import Certificates.Certificate16039

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

namespace CertificateChecks.Batch16011

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

private theorem frameWords_letters_0 : ∀ i < 10, ∀ k ∈ Native.frameWords[i]!, k = 2 ∨ k = 3 := by
  decide +kernel

end CertificateChecks.Batch16011

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix in
theorem certificate16011 : ∀ i < 10, ∀ k ∈ Native.frameWords[i]!, k = 2 ∨ k = 3 := by
  exact CertificateChecks.Batch16011.frameWords_letters_0

end Certificates
