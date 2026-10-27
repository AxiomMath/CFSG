module

public meta import Certificates.Kernel.SporSch.Co1.GenDag
meta import Certificates.Kernel.Co1B.In25170
public import Certificates.Kernel.SporSch.Co1.GenDag
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelCo1B.Comm25170.CD CertificateChecks.KernelCo1B.Comm25170.dagC

namespace CertificateChecks.KernelCo1B.Comm25170.CD

@[expose] def KW : List (List Nat) :=
  [[8, 7, 9, 7, 2, 4, 2, 6, 9, 3, 7, 3, 5], [9, 7, 5, 2, 6, 2, 6, 9, 3, 7, 3]]

end CertificateChecks.KernelCo1B.Comm25170.CD

end
