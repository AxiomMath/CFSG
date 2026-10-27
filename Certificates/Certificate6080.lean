module

import Certificates.Kernel.KDenseP.TwoPoint.Th
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Existence.TwoPoint.ThData

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6080 : ∀ i ∈ List.range 8, wordLin (thWAlpha ++ thWU[i]!) = wordLin (thWU[i]! ++ thWAlpha) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6080

end Certificates
