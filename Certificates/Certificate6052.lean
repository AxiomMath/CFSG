
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6052 : ∀ i ∈ [1, 3, 16, 20, 28, 32, 46, 51], wordLin (fiRelW rels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6052

end Certificates
