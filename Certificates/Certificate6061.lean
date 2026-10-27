
module


public import CFSG.Monster.Existence.TwoPoint.Fi23S4Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6061 : wordLin (s4WGamma ++ s4WGamma) = 1 ∧ wordLin (fiWU[8]! ++ fiWU[8]!) = 1 ∧
    wordLin (s4WGamma ++ fiWBeta) = wordLin (fiWBeta ++ s4WGamma) ∧
    wordLin (s4WE8Gamma ++ s4WE8Gamma ++ s4WE8Gamma) = 1 ∧
    wordLin (s4WAlphaGamma ++ s4WAlphaGamma ++ s4WAlphaGamma) = 1 ∧
    wordLin s4WE8Gamma ≠ 1 ∧ wordLin s4WAlphaGamma ≠ 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6061

end Certificates
