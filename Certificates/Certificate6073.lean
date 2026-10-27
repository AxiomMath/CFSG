module

public import CFSG.Monster.Existence.TwoPoint.HNCheck
import Certificates.Kernel.KDenseP.TwoPoint.HN

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6073 : wordLin (hnRhoT ++ hnCAlpha) = wordLin (hnCAlpha ++ hnWAlpha) ∧
    wordLin (hnRhoT ++ hnCBeta) = wordLin (hnCBeta ++ hnWBeta) ∧ wordLin hnWAB5 = 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6073

end Certificates
