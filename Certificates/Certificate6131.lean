module

public import Certificates.Data.Seitz77Sec27L34Ord3
public meta import Certificates.Data.Seitz77Sec27L34Ord3
import Certificates.Kernel.PermCent.K6131Glue

public section

namespace Certificates

theorem certificate6131 : Seitz77Sec27.l34Ord3Check = true :=
  CFSG.Certificates.Kernel.PkCV.L34O3.check6131

end Certificates
