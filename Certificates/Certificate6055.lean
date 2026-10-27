
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels) in
theorem certificate6055 : wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6055

end Certificates
