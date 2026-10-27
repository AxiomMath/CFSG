module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6084 : ∀ i ∈ [13],
    wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6084

end Certificates
