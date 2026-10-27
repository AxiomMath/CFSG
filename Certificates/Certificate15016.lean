module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
import Certificates.Kernel.LocalComp.M12End.Facts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndData

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M12 in
theorem certificate15016 : m12EndCheck m12S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true :=
  KernelLC.M12End.m12EndCheck_eq_true

end Certificates
