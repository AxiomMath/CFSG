module

public import Certificates.Data.S7SocM12

public section

open Certificates.S7SocM12

namespace CertificateChecks.Batch517103

open Certificates.S7SocM12

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m12_soc_517103_0 : QSM.check = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m12_soc_517103_1 : QSM.orderCertificate = 128 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m12_soc_517103_2 : m12SocGens () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem m12_soc_517103_3 : m12SocCheck () = true := by
  decide +kernel

end CertificateChecks.Batch517103

namespace Certificates

open CertificateChecks

open Certificates.S7SocM12 in
theorem certificate517103 : (QSM.check = true ∧ QSM.orderCertificate = 128) ∧ m12SocGens () = true ∧
    m12SocCheck () = true :=
  ⟨⟨CertificateChecks.Batch517103.m12_soc_517103_0, CertificateChecks.Batch517103.m12_soc_517103_1⟩,
    CertificateChecks.Batch517103.m12_soc_517103_2, CertificateChecks.Batch517103.m12_soc_517103_3⟩

end Certificates
