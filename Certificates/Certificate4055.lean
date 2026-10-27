module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert1Inputs
import Certificates.Kernel.LocalQT.Lat.C4055
import CFSG.Certificates.Kernel.LocalQTLatGSound
import CFSG.Certificates.Kernel.LocalQTLatSixCSound

public section

namespace Certificates

open CFSG.KD.LQT.C4055 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23.C1 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 CFSG.QuasithinUnique.A5.G3.M23.C1 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate4055 : (cert.check RN.enc = true)
    ∧ (cert.tleOK RN.enc = true)
    ∧ (latSixCheck cert [aData1] = true) :=
  ⟨CFSG.KC.LQT.CM.latG_sound (by decide) C MW 5 [] 0 ms 4 labT inj injM cert
      (CFSG.KC.LQT.L.latG_intro p0 p1 p2 p3 p4 p5 p6 p7 p8),
    CFSG.KC.LQT.CM.tleT_sound (by decide) C inj MW 5 [] 0 cert ht,
    CFSG.KC.LQT.CM.latSix_sound (by decide) C inj msX cert [aData1] hs⟩

end Certificates
