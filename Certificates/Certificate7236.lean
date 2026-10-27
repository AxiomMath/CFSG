module

public import Certificates.Data.HZ82.L34
import CFSG.Certificates.Kernel.Spor.MathieuSound
import Certificates.Kernel.MathieuFam.Checks7236

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Mathieu.Native CFSG.Quasithin.H.L34Z.Native in
theorem certificate7236 : check 512 l34Data = true :=
  CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.l34K

end Certificates
