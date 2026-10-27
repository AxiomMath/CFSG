
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6051 : ∀ i ∈ [5, 13, 24, 27, 31, 37, 39, 40, 49], wordLin (fiRelW rels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6051

end Certificates
