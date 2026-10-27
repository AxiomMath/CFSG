module

import Certificates.Kernel.KDenseP.TwoPoint.Th
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Existence.TwoPoint.ThData

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6081 : ∀ i ∈ List.range 8, wordLin (thWBeta ++ thWU[i]!) = wordLin (thWU[i]! ++ thWBeta) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6081

end Certificates
