module

public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.D42Tri.P0Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate29530 : ∀ g ∈ CFSG.Sporadic.SmallOddCore.genOf 360
      (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.k2Tbls ()), g ^ 9 = 1 → g ^ 3 = 1 := KernelD42Tri.p0_k2_nine

end Certificates
