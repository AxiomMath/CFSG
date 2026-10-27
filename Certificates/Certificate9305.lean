module

public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

namespace CertificateChecks.Batch9305

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m22_cqCheck : cqCheck m22Rep1 (enumerationTab m22CentQ1) = true := by
  decide +kernel

end CertificateChecks.Batch9305

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution in
theorem certificate9305 : cqCheck m22Rep1 (enumerationTab m22CentQ1) = true := by
  exact CertificateChecks.Batch9305.m22_cqCheck

end Certificates
