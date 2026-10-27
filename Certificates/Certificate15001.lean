module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLPk
import Certificates.Kernel.Census.McLProof

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.McL in
theorem certificate15001 : mclCheckW mclSG mclRoots mclNodes mclCS mclWCS = true :=
  KernelCensus.McLK.mclCheckW_eq_true_proved

end Certificates

end
