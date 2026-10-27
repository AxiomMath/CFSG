module

public import Certificates.Data.TabSuzC
public meta import Certificates.Data.TabSuzC
import Certificates.Kernel.SuzC17323.Facts
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabSuzC in
theorem certificate17323 : tabSuzCCheck () = true :=
  KernelSuzC17323.tabSuzC_ok

end Certificates
