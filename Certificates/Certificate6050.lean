
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6050 : ∀ i ∈ [4, 11, 14, 22, 29, 35, 38, 45, 53], wordLin (fiRelW rels[i]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6050

end Certificates
