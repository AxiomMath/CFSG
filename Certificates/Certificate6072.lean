module

import Certificates.Kernel.KDenseP.TwoPoint.Gx
public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBCheckBase

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6072 : wordLin (gxXWord ++ gxCW9) = wordLin (gxCW9 ++ gxProdWord (gxXList 9)) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6072

end Certificates
