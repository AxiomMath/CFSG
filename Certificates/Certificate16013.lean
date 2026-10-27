module

public import Certificates.Certificate16017

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix)

namespace CertificateChecks.Batch16013

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix)

private theorem signedMatrix_two_0 : signedMatrix id (fun _ => 2) = -1 := by
  decide +kernel

end CertificateChecks.Batch16013

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
open CFSG.Sporadic.SmallF2 (rowsMatrix) in
theorem certificate16013 : signedMatrix id (fun _ => 2) = -1 := by
  exact CertificateChecks.Batch16013.signedMatrix_two_0

end Certificates
