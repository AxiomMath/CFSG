module

public import CFSG.Monster.Existence.TwoPoint.HNCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels) in
theorem certificate6078 : ∀ i ∈ [16, 17, 18], wordLin (hnRelW hnRels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6078

end Certificates
