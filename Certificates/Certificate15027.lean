module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
import Certificates.Kernel.LocalComp.Fi24TwoB.T15027

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime in
theorem certificate15027 : fi24TwoBKCheck = true := by
  unfold fi24TwoBKCheck
  rw [KernelLC.Fi24B.chainsOK, KernelLC.Fi24B.nOK, KernelLC.Fi24B.transOK, KernelLC.Fi24B.qOK]
  rfl

end Certificates
