module

public import Certificates.Kernel.MonsterB.Chain3025Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 in
theorem certificate3025 : Native.co2ChainCertOK = true :=
  Chain3025.co2ChainCertOK_true

end Certificates
