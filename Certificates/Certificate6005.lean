module

public import CFSG.Monster.AxisCount.BabyInv
import Certificates.Kernel.KDenseP.Axis.C6005

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby in
theorem certificate6005 : Function.Injective fun j : Fin 10 => (xStarCoord (CFSG.Monster.AxisCount.Baby.vv j), trA2 (CFSG.Monster.AxisCount.Baby.vv j)) :=
  CertificateChecks.KernelKDenseP.Axis.c6005

end Certificates
