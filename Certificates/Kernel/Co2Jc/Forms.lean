module

public import CFSG.Sporadic.Co2Jc.Native.Forms

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCo2Jc

theorem forms_check : CFSG.Sporadic.Co2Jc.Native.formsOK = true := by
  decide +kernel

end CertificateChecks.KernelCo2Jc
