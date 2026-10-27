module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33Inputs
import Certificates.Kernel.LocalQT.Lat.C4125
import CFSG.Certificates.Kernel.LocalQTLatKSound

public section

namespace Certificates

open CFSG.KD.LQT.C4125 CFSG.QuasithinUnique.Bridge.Over.CertU33 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.Bridge.Over.CertU33 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127 CFSG.Blueprint in
theorem certificate4125 : (cert.check RN.enc = true)
    ∧ (memberOK cert cts = true)
    ∧ (cert.tleOK RN.enc = true) :=
  ⟨CFSG.KC.LQT.LK.lat_sound (by decide) cert hl, CFSG.KC.LQT.LK.member_sound (by decide) cert cts hm,
    CFSG.KC.LQT.LK.tle_sound (by decide) cert p6⟩

end Certificates
