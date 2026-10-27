module

public import Certificates.Data.HZ82.Code22
import CFSG.Certificates.Kernel.Spor.MathieuSound
import Certificates.Kernel.MathieuFam.Checks7228

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native CFSG.Quasithin.H.Code22.Native in
theorem certificate7228 : check 24 l22Data = true :=
  CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.l22K

end Certificates
