module

import Certificates.Kernel.KDenseP.TwoPoint.Gx
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.B.Short CFSG.Monster.Existence in
theorem certificate6065 : wordLin (gxYWord 9 ++ gxBPWord) aStar ≠ wordLin (gxYWord 9) aStar ∧
    wordLin (gxYWord 10 ++ fiWAlpha) aStar ≠ wordLin (gxYWord 10) aStar ∧
    wordLin (gxYWord 10 ++ gxBPWord) aStar ≠ wordLin (gxYWord 10) aStar :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6065

end Certificates
