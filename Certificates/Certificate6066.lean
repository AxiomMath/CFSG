module

import Certificates.Kernel.KDenseP.TwoPoint.Gx
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.B.Short CFSG.Monster.Existence in
theorem certificate6066 : ∀ j ∈ [11, 12],
    wordLin (gxYWord j ++ fiWAlpha) aStar ≠ wordLin (gxYWord j) aStar ∧
      wordLin (gxYWord j ++ gxBPWord) aStar ≠ wordLin (gxYWord j) aStar :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6066

end Certificates
