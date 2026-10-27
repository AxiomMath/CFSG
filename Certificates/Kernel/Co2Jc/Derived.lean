module

public import CFSG.Sporadic.Co2Jc.Native.Derived

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCo2Jc

theorem derived_check : CFSG.Sporadic.Co2Jc.Native.derivedOK = true := by
  decide +kernel

end CertificateChecks.KernelCo2Jc
