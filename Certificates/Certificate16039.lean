module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Co2Cert.Text5
public import Certificates.Certificate3138
public import Certificates.Data.CFSGNative.Co2Smith.Data

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

namespace CertificateChecks.Batch16039

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

private theorem chainGens_letters_0 : ∀ k < 6, ∀ i < (Native.chainGens[k]!).size,
    ∀ x ∈ (Native.chainGens[k]!)[i]!, x = 2 ∨ x = 3 := by
  decide +kernel

end CertificateChecks.Batch16039

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix in
theorem certificate16039 : ∀ k < 6, ∀ i < (Native.chainGens[k]!).size,
    ∀ x ∈ (Native.chainGens[k]!)[i]!, x = 2 ∨ x = 3 := by
  exact CertificateChecks.Batch16039.chainGens_letters_0

end Certificates
