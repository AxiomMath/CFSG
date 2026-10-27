module

public import CFSG.Monster.Existence.TwoPoint.Fi22Check
import Certificates.Kernel.KDenseP.TwoPoint.Fi
import Certificates.Kernel.KDenseP.TwoPoint.FiImg

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6046 : (wordLin (fiRhoT ++ fiCGamma) = wordLin (fiCGamma ++ fiWU[0]!) ∧
      wordLin (fiRhoT ++ fiCDelta) = wordLin (fiCDelta ++ fiWDelta)) ∧
    fiImgConjCheck 0 27 = true :=
  ⟨CertificateChecks.KernelKDenseP.TwoPoint.c6046, CertificateChecks.KernelKDenseP.TwoPoint.fiImgConj_ok⟩

end Certificates
