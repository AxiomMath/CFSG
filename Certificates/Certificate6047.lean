
module


public import CFSG.Monster.Existence.TwoPoint.Fi23Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6047 : wordLin (fiRhoT ++ fiCAlpha) = wordLin (fiCAlpha ++ fiWAlpha) ∧
    wordLin (fiWAB ++ fiCThreeA) = wordLin (fiCThreeA ++ wordThreeA) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6047

end Certificates
