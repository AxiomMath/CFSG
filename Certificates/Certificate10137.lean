module

public import Certificates.Data.Fi23Moore
import Certificates.Kernel.Fi23Five.MooreGlue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23.Native in
theorem certificate10137 :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.fi23FiveMooreOK (orbitData ()) = true := KernelFi23Five.moore_ok

end Certificates
