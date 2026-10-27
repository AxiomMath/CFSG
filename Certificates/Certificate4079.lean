module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12Inputs
import Certificates.Kernel.LocalQT.Lat.C4079
import CFSG.Certificates.Kernel.LocalQTLatGSound

public section

namespace Certificates

open CFSG.KD.LQT.C4079 CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M12Lat in
open Equiv PermLat in
theorem certificate4079 : (cert.check RN.enc = true) :=
  CFSG.KC.LQT.CM.latG_sound (by decide) C MW 2 TW 46 ms 2 labT inj injM cert
    (CFSG.KC.LQT.L.latG_intro p0 p1 p2 p3 p4 p5 p6 p7 p8)

end Certificates
