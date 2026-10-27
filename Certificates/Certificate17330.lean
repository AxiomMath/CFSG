module

public import Certificates.Data.TabCo1ThreeB
public meta import Certificates.Data.TabCo1ThreeB
import Certificates.Kernel.Co1B.C17330

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB in
theorem certificate17330 : CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.threeBCheck () = true := KernelCo1B.Bound17330.c17330

end Certificates
