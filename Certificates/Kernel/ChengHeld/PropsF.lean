module

public import Certificates.Kernel.ChengHeld.PropsS4F
public import Certificates.Kernel.ChengHeld.PropsS2F

public section

namespace CertificateChecks.KernelChengHeld.P

open CFSG.OddStandard.ChengHeldData

theorem chProps_true : chPropsOK = true := by
  unfold chPropsOK
  rw [struct4_0, struct4_1, struct2, aut0, aut1, aut2, gAut0, gAut1, gAut2]
  rfl

end CertificateChecks.KernelChengHeld.P

end
