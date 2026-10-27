
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6053 : ∀ i ∈ [10, 12, 15, 25, 33, 34, 36, 42, 50, 54], wordLin (fiRelW rels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6053

end Certificates
