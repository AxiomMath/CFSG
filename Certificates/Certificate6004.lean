module

public import CFSG.Monster.AxisCount.BabyIdent
import Certificates.Kernel.KDenseP.Axis.C6004

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Baby in
theorem certificate6004 : OrbitIdent 0 ∧ OrbitIdent 1 ∧ OrbitIdent 2 ∧ OrbitIdent 7 ∧ OrbitIdent 9 :=
  CertificateChecks.KernelKDenseP.Axis.c6004

end Certificates
