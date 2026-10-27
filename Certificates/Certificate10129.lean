module

public import Certificates.Data.Fi23FiveFix
import Certificates.Kernel.Fi23Five.FixGlue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23.Native in
theorem certificate10129 :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.fi23FiveFixOK (orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23Five.fiveFix_ok

end Certificates
