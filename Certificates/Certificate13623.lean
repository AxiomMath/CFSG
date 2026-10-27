module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs
import Certificates.Kernel.Fi23Klein.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23.Native in
theorem certificate13623 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.kleinOK (orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23Klein.klein_ok

end Certificates
