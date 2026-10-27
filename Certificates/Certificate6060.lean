
module


public import CFSG.Monster.Existence.TwoPoint.Fi23S4Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6060 : wordLin (fiRhoT ++ s4CGamma) = wordLin (s4CGamma ++ s4WGamma) ∧
    wordLin (fiRhoT ++ s4CBetaGamma) = wordLin (s4CBetaGamma ++ s4WBetaGamma) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6060

end Certificates
