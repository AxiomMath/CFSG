module

public import Certificates.Data.Kernel.Cert690.Sq

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

set_option maxHeartbeats 0 in
theorem root1 : (innTab (2 * innW (compTab (liftTab 34647329153 0) (liftTab 34647329153 0))) ==
    compTab (liftTab 34647329153 0) (liftTab 34647329153 0)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem root2 : (innTab (2 * innW (compTab (liftTab 35704297409 0) (liftTab 35704297409 0))) ==
    compTab (liftTab 35704297409 0) (liftTab 35704297409 0)) = true := by decide +kernel

theorem invR : isInvCode 34647329153 = true ∧ isInvCode 35704297409 = true ∧
    isInvCode Code.one = false := by decide +kernel

theorem isoGens : a8Gens.all (isoQ false) = true ∧ isoQ false Code.one = true := by
  decide +kernel

end CertificateChecks.KernelC690.SqPass

end
