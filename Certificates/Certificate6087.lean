module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6087 : ∀ i ∈ [5, 32, 37],
    wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6087

end Certificates
