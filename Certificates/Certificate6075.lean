module

public import CFSG.Monster.Existence.TwoPoint.HNCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels) in
theorem certificate6075 : ∀ i ∈ [4, 5, 6, 7, 10, 11, 12], wordLin (hnRelW hnRels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6075

end Certificates
