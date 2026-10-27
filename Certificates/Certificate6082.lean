module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsDefs
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6082 : (wordLin (thRhoT ++ thCAlpha) = wordLin (thCAlpha ++ thWAlpha) ∧
      wordLin (thRhoT ++ thCBeta) = wordLin (thCBeta ++ thWBeta)) ∧
    wordLin (wordThreeC ++ thWG) = wordLin (thWG ++ thWAB) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6082

end Certificates
