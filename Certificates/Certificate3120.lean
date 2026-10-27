module

public import Certificates.Data.CFSGNative.Mathieu.M11
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic

public section

open CFSG.Sporadic.Mathieu.Native

namespace CertificateChecks.Batch3120

open CFSG.Sporadic.Mathieu.Native

private theorem m11_check_0 : check 11 m11Data = true := by
  decide +kernel

end CertificateChecks.Batch3120

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native in
theorem certificate3120 : check 11 m11Data = true := by
  exact CertificateChecks.Batch3120.m11_check_0

end Certificates
