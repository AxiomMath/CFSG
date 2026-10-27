
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6054 : ∀ i ∈ [2, 6, 8, 18, 19, 23, 30, 43, 44], wordLin (fiRelW rels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6054

end Certificates
