module

public import Certificates.Data.TabCo1ThreeD
public meta import Certificates.Data.TabCo1ThreeD
import Certificates.Kernel.Co1B.C17590

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD in
theorem certificate17590 : threeDFix () = 256 := KernelCo1B.Fix17590.c17590

end Certificates
