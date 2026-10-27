module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22DataInputs
import Certificates.Kernel.LocalQT.Lat.C4106
import CFSG.Certificates.Kernel.LocalQTLatSixCSound
import CFSG.Certificates.Kernel.LocalQTTleTSound

public section

namespace Certificates

open CFSG.KD.LQT.C4106 CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  CFSG.QuasithinUnique.A5.G3 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 in
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
theorem certificate4106 : (latSixCheck cert [m22AData] = true)
    ∧ (cert.tleOK RN.enc = true) :=
  ⟨CFSG.KC.LQT.CM.latSix_sound (by decide) CFSG.KD.LQT.C4053.C CFSG.KD.LQT.C4053.inj ms cert
      [m22AData] hs,
    CFSG.KC.LQT.CM.tleT_sound (by decide) CFSG.KD.LQT.C4053.C CFSG.KD.LQT.C4053.inj
      CFSG.KD.LQT.C4053.MW 2 CFSG.KD.LQT.C4053.TW 38 cert ht⟩

end Certificates
