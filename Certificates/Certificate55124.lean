module

public import Certificates.Data.M12CenterQuat

public section

open CFSG.ClassicalInvolution.Q3.TL4.E3S3MC

namespace CertificateChecks.Batch55124

open CFSG.ClassicalInvolution.Q3.TL4.E3S3MC

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem chk_quat0 : chkQuat0 () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem chk_quat1 : chkQuat1 () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem chk_fix2 : chkFix2 () = true := by
  decide +kernel

end CertificateChecks.Batch55124

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.E3S3MC in
theorem certificate55124 : chkQuat0 () = true ∧ chkQuat1 () = true ∧ chkFix2 () = true :=
  ⟨CertificateChecks.Batch55124.chk_quat0, CertificateChecks.Batch55124.chk_quat1, CertificateChecks.Batch55124.chk_fix2⟩

end Certificates
