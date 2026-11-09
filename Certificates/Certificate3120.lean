module

public import Certificates.Data.CFSGNative.Mathieu.M11
import Certificates.Data.Kernel.Spor.Mathieu
import CFSG.Certificates.Kernel.Spor.MathieuSound
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic

public section

open CFSG.Sporadic.Mathieu.Native

namespace CertificateChecks.Batch3120

open CFSG.Sporadic.Mathieu.Native

private theorem m11_check_0K : CFSG.KS.Mathieu.mcheck 11 4 m11Data = true := by quickRfl

private theorem m11_check_0 : check 11 m11Data = true :=
  CFSG.KS.Mathieu.mcheck_sound (by decide) m11_check_0K

end CertificateChecks.Batch3120

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native in
theorem certificate3120 : check 11 m11Data = true := by
  exact CertificateChecks.Batch3120.m11_check_0

end Certificates
