module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32Inputs
import Certificates.Kernel.LocalQT.Lat.C4124
import CFSG.Certificates.Kernel.LocalQTLatKSound

public section

namespace Certificates

open CFSG.KD.LQT.C4124 CFSG.QuasithinUnique.Bridge.Over.CertL32 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.Bridge.Over.CertL32 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L in
theorem certificate4124 : (cert.check RN.enc = true)
    ∧ (memberOK cert cts = true)
    ∧ (cert.tleOK RN.enc = true) :=
  ⟨CFSG.KC.LQT.LK.lat_sound (by decide) cert hl, CFSG.KC.LQT.LK.member_sound (by decide) cert cts hm,
    CFSG.KC.LQT.LK.tle_sound (by decide) cert p6⟩

end Certificates
