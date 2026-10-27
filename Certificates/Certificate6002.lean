module

public import CFSG.Monster.AxisCount.BabyIdent
import Certificates.Kernel.KDenseP.Axis.C6002

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby in
theorem certificate6002 : OrbitIdent 4 ∧ OrbitIdent 5 :=
  CertificateChecks.KernelKDenseP.Axis.c6002

end Certificates
