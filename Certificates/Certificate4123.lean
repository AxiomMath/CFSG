module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenCertDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5Inputs
import Certificates.Kernel.LocalQT.Lat.C4123
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTLatKSound

public section

namespace Certificates

open CFSG.KD.LQT.C4123 CFSG.QuasithinUnique.Bridge.Over.CertA5 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.Bridge.Over.CertA5 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127 in
theorem certificate4123 : (cert.check RN.enc = true)
    ∧ (memberOK cert cts = true)
    ∧ (∀ g ∈ mGens, Equiv.Perm.sign g = 1)
    ∧ (∀ g ∈ tGens, Equiv.Perm.sign g = 1) :=
  ⟨CFSG.KC.LQT.LK.lat_sound (by decide) cert hl, CFSG.KC.LQT.LK.member_sound (by decide) cert cts hm,
    by decide +kernel, by decide +kernel⟩

end Certificates
