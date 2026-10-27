module

public import CFSG.Monster.AxisCount.BabyIdent
import Certificates.Kernel.KDenseP.Axis.C6003

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby in
theorem certificate6003 : OrbitIdent 3 ∧ OrbitIdent 6 ∧ OrbitIdent 8 :=
  CertificateChecks.KernelKDenseP.Axis.c6003

end Certificates
