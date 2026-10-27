
module


import Certificates.Kernel.KDenseP.TwoPoint.Fi
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Existence.TwoPoint.Fi23Data
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Data

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6059 : ∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9],
    wordLin (s4WGamma ++ fiWU[i]!) = wordLin (fiWU[i]! ++ s4WGamma) :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6059

end Certificates
