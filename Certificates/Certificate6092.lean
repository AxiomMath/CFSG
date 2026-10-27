module

public import CFSG.Monster.Existence.TwoPoint.ThreeVCheck
import Certificates.Kernel.KDenseP.TwoPoint.Fi

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6092 : wordLin (fiRhoT ++ fiCAlphaGamma) = wordLin (fiCAlphaGamma ++ fiWAlphaGamma) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6092

end Certificates
