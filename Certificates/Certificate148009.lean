module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WM24Inputs
import Certificates.Kernel.Ronan148.WM24InvFacts

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec14.Ronan148W in
theorem certificate148009 : invCheck () = true :=
  CertificateChecks.KernelRonan148.WM24Inv.invCheck_true

end Certificates
