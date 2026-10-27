module

public import Certificates.Data.M163M12

public section

open CFSG.ClassicalInvolution.Q3.TL4.MF163

namespace CertificateChecks.Batch55110

open CFSG.ClassicalInvolution.Q3.TL4.MF163

set_option maxHeartbeats 0 in
private theorem m12_quat_check : m12QuatCheck = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem m12_noRoot2_check : m12NoRoot2Check = true := by
  decide +kernel

end CertificateChecks.Batch55110

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.TL4.MF163 in
theorem certificate55110 : m12QuatCheck = true ∧ m12NoRoot2Check = true := by
  exact ⟨CertificateChecks.Batch55110.m12_quat_check, CertificateChecks.Batch55110.m12_noRoot2_check⟩

end Certificates
