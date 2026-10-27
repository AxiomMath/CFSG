module

public import Certificates.Data.YamakiPres

public section

open CFSG.ClassicalInvolution.Solomon73.Yamaki

namespace CertificateChecks.Batch550702

open CFSG.ClassicalInvolution.Solomon73.Yamaki

private theorem spInvolCheck_holds : spInvolCheck () = true := by
  decide +kernel

private theorem spSympCheck_holds : spSympCheck () = true := by
  decide +kernel

private theorem spRelCheck_holds : spRelCheck () = true := by
  decide +kernel

private theorem spTransvCheck_holds : spTransvCheck () = true := by
  decide +kernel

private theorem spOrbitCheck_holds : spOrbitCheck () = true := by
  decide +kernel

private theorem spCoverCheck_holds : spCoverCheck () = true := by
  decide +kernel

end CertificateChecks.Batch550702

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550702 :
    (spInvolCheck () = true)
    ∧ (spSympCheck () = true)
    ∧ (spRelCheck () = true)
    ∧ (spTransvCheck () = true)
    ∧ (spOrbitCheck () = true)
    ∧ (spCoverCheck () = true) :=
  ⟨CertificateChecks.Batch550702.spInvolCheck_holds, CertificateChecks.Batch550702.spSympCheck_holds, CertificateChecks.Batch550702.spRelCheck_holds,
    CertificateChecks.Batch550702.spTransvCheck_holds, CertificateChecks.Batch550702.spOrbitCheck_holds,
    CertificateChecks.Batch550702.spCoverCheck_holds⟩

end Certificates
