module

public import Certificates.Data.TabSuzFuse
public meta import Certificates.Data.TabSuzFuse
import Certificates.Kernel.SuzFuse17320.Facts
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse in
theorem certificate17320 : CFSG.HardMathSupport.Dickson.I271.TabSuzFuse.fuseCheck () = true :=
  KernelSuzFuse17320.fuse_ok

end Certificates
