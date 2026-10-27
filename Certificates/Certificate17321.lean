module

public import Certificates.Data.TabSuzA
public meta import Certificates.Data.TabSuzA
import Certificates.Kernel.SuzA17321.Facts
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabSuzA in
theorem certificate17321 : caseACheck () = true :=
  KernelSuzA17321.caseA_ok

end Certificates
