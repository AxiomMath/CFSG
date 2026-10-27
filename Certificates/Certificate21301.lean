module

public import CFSG.Holt.SmallGroupsCheck
import CFSG.Certificates.Kernel.Spor.MathieuSound
import Certificates.Kernel.MathieuFam.Checks21301

public section

namespace Certificates

open CertificateChecks

theorem certificate21301 : CFSG.Sporadic.Mathieu.Native.check 11 CFSG.Holt.SmallGroups.m11Data4 = true :=
  CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.m11Data4K

end Certificates
