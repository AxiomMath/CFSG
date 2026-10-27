module

public import Certificates.Kernel.A312M23.Data
public import Certificates.Kernel.M23Dc.Data
public import Certificates.Data.Kernel.A312M23K
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.A312M23

@[expose] noncomputable def AB : List (List Nat) := CFSG.KD.M23Dc.J.tabs.take 2

@[expose] noncomputable def Sg : List (List Nat) := (CFSG.KD.M23Dc.J.tabs.drop 2).take 3

@[expose] noncomputable def gw (j : Nat) : List (List Nat) := [(CFSG.KD.M23Dc.J.mw.getD j []).headD []]

end CFSG.KD.A312M23

open CFSG.KC.A312M23K CFSG.KD.A312M23

#kc_each CFSG.KD.A312M23 ch4170y1_
  (fun _ => m22Chk y1T AB Sg (gw 1) 23 y1Bl y1Bi y1WA y1WB y1GA y1GB) 0 1

#kc_each CFSG.KD.A312M23 ch4170y2_
  (fun k => l34Part y2T AB Sg (gw 2) 23 y2Xs y2Tq y2Ws y2Wcj y2Wu y2Wv y2Rel y2Wxs k) 0 4

#kc_each CFSG.KD.A312M23 ch4170y3_ (fun k => e2Part y3T AB Sg (gw 3) 23 y3Xs y3Tq y3Ws y3V
  y3Wit y3Ex y3Bl y3Bi 360 y3Sp false y3Cw false y3Wcj y3B k) 0 11

#kc_each CFSG.KD.A312M23 ch4170y4_ (fun k => e2Part y4T AB Sg (gw 4) 23 y4Xs y4Tq y4Ws y4V
  y4Wit y4Ex y4Bl y4Bi 168 y4Sp true y4Cw false y4Wcj y4B k) 0 9

#kc_each CFSG.KD.A312M23 ch4170y5_ (fun k => e2Part y5T AB Sg (gw 5) 23 y5Xs y5Tq y5Ws y5V
  y5Wit y5Ex y5Bl y5Bi 2520 y5Sp false y5Cw false y5Wcj y5B k) 0 9

#kc_each CFSG.KD.A312M23 ch4170y6_ (fun k => e2Part y6T AB Sg (gw 6) 23 y6Xs y6Tq y6Ws y6V
  y6Wit y6Ex y6Bl y6Bi 168 y6Sp true y6Cw true y6Wcj y6B k) 0 9

#kc_each CFSG.KD.A312M23 ch4170y7_ (fun k => e2Part y7T AB Sg (gw 7) 23 y7Xs y7Tq y7Ws y7V
  y7Wit y7Ex y7Bl y7Bi 60 y7Sp false y7Cw true y7Wcj y7B k) 0 11

#kc_each CFSG.KD.A312M23 ch4170y9_ (fun k => e2Part y9T AB Sg (gw 9) 23 y9Xs y9Tq y9Ws y9V
  y9Wit y9Ex y9Bl y9Bi 60 y9Sp false y9Cw true y9Wcj y9B k) 0 11

#kc_each CFSG.KD.A312M23 ch4170y8_ (fun _ => triChk y8T AB Sg (gw 8) 23 y8Bl y8Bi y8X) 0 1

end
