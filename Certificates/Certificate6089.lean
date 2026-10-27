module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6089 : ∀ i ∈ [1, 10, 12, 18, 24, 25, 26, 28, 30, 31, 34, 36],
    wordLin (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6089

end Certificates
