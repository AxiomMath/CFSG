module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8Inputs
import Certificates.Kernel.LocalQT.Lat.C4071
import CFSG.Certificates.Kernel.LocalQTLatCCheckSound

public section

namespace Certificates

open CFSG.KD.LQT.C4071 CFSG.QuasithinUnique.L246C127.Even8 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.L246C127.Even8 in
open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate4071 : (cert.check RN.enc = true)
    ∧ (memberOK cert cts = true)
    ∧ (∀ g ∈ mGens, Equiv.Perm.sign g = 1)
    ∧ (∀ g ∈ tGens, Equiv.Perm.sign g = 1) :=
  ⟨CFSG.KC.LQT.CM.latC_sound (by decide) C CFSG.KD.LQT.C4071.inj MW ms cert hl,
    CFSG.KC.LQT.CM.memberC_sound (by decide) C CFSG.KD.LQT.C4071.inj ms cert cts hm,
    CFSG.KC.LQT.LK.signs_sound (by decide) mGens sm,
    CFSG.KC.LQT.LK.signs_sound (by decide) tGens st⟩

end Certificates
