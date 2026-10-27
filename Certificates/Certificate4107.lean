module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert2Inputs
import Certificates.Kernel.LocalQT.Lat.C4107
import CFSG.Certificates.Kernel.LocalQTLatSixCSound

public section

namespace Certificates

open CFSG.KD.LQT.C4107 CFSG.QuasithinUnique.A5.G3.M23.C2 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 CFSG.QuasithinUnique.A5.G3.M23.C2 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate4107 : (cert.check RN.enc = true)
    ∧ (cert.tleOK RN.enc = true)
    ∧ (latSixCheck cert [aData1, aData2] = true) :=
  ⟨CFSG.KC.LQT.CM.latC_sound (by decide) C CFSG.KD.LQT.C4107.inj MW ms cert hl,
    CFSG.KC.LQT.CM.tleCC_sound (by decide) C CFSG.KD.LQT.C4107.inj MW cert ht,
    CFSG.KC.LQT.CM.latSix_sound (by decide) C CFSG.KD.LQT.C4107.inj ms cert [aData1, aData2] hs⟩

end Certificates
