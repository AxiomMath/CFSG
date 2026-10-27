module

public import CFSG.Quasithin.H13.A5M12Inputs
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Data

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

namespace Certificates

set_option maxHeartbeats 0 in
open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 in
theorem certificate7105 :
    (∀ a ∈ cent12H ++ cent12S, inAutOK a = true ∧ permM a dodecadMask = dodecadMask)
    ∧ (∀ a ∈ cent12H, actC12 a 360 = 360)
    ∧ (∀ m < 1024, (∀ a ∈ cent12H, actC12 a m = m) → m = 0 ∨ m = 360)
    ∧ (∀ m < 1024, m ∈ combos (cent12S.map fun a => actC12 a 360))
    ∧ (inAutOK tau12 = true ∧ permM tau12 dodecadMask = dodecadMask ^^^ (2 ^ 24 - 1)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end Certificates
