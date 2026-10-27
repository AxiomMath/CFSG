module

public import CFSG.Monster.Existence.TwoPoint.HNTwoBCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6079 : wordLin (hnXWord ++ hnCW) = wordLin (hnCW ++ hnWW) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6079

end Certificates
