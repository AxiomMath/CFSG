module

public import Certificates.Data.Kernel.D5TwistF

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

theorem ch712503L_ok : ch712503L () = true := by decide +kernel

theorem ch712503SF_ok : ch712503SF () = true := by decide +kernel

theorem ch712503AF_ok : ch712503AF () = true := by decide +kernel

end Certificates.D5TwistK

end
