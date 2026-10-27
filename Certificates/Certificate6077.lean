module

public import CFSG.Monster.Existence.TwoPoint.HNCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels) in
theorem certificate6077 : ∀ i ∈ [13, 14, 15], wordLin (hnRelW hnRels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6077

end Certificates
