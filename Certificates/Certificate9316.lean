module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22E8Data
import Certificates.Kernel.SmallSpor.M22E8Glue
public import CFSG.ClassicalInvolution.PerfectCase.Basic

public section

namespace CertificateChecks.Batch9316

theorem m22E8_check : CFSG.ClassicalInvolution.m22E8Check = true :=
  KernelSmallSpor.M22.check9316

end CertificateChecks.Batch9316

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native in
theorem certificate9316 : m22E8Check = true := CertificateChecks.Batch9316.m22E8_check

end Certificates
