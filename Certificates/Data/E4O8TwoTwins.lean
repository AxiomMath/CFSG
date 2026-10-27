module

public import Certificates.Data.E4QuatO8Check

public section

namespace Certificates.E4O8TwoTwins

open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4O8

@[expose] def check (_ : Unit := ()) : Bool :=
  let L := L0A ()
  let u := u0A ()
  let v := v0A ()
  let ws := wsW ()
  let w₁ := omegaW (ws.getD 1 [])
  let w₃ := omegaW (ws.getD 3 [])
  edgeCheckA 360 L u v w₃ && !normsA 360 L u v (compA 360 (invCand 360 w₁) w₃)

end Certificates.E4O8TwoTwins
