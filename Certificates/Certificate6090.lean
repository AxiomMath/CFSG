module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6090 : ∀ i ∈ [4, 6, 11, 15, 17, 20, 21, 23, 27, 29],
    wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6090

end Certificates
