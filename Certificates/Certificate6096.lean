module

public import CFSG.Monster.Existence.TwoPoint.Y433MCheck
import Certificates.Kernel.KDenseP.TwoPoint.Misc

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6096 : wordLin (y433RelW y433SpiderR) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6096

end Certificates
