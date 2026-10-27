module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6Inputs
import Certificates.Kernel.LocalQT.Lat.C4130
import CFSG.Certificates.Kernel.LocalQTLatKSound

public section

namespace Certificates

open CFSG.KD.LQT.C4130 CFSG.QuasithinUnique.L246C127.Even6 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.L246C127.Even6 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate4130 : (cert.check RN.enc = true)
    ∧ (memberOK cert cts = true)
    ∧ (∀ g ∈ mGens, Equiv.Perm.sign g = 1)
    ∧ (∀ g ∈ tGens, Equiv.Perm.sign g = 1) :=
  ⟨CFSG.KC.LQT.LK.lat_sound (by decide) cert hl, CFSG.KC.LQT.LK.member_sound (by decide) cert cts hm,
    by decide +kernel, by decide +kernel⟩

end Certificates
