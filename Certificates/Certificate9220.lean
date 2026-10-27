module

public import CFSG.Sporadic.Bridge.ThSurjInputs
import CFSG.Certificates.Kernel.Th.SoundnessTwin
import CFSG.Certificates.Kernel.Th.Checks2.Surj_K
import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
public import CFSG.Sporadic.Bridge.ThData

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Th in
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native TauCeti in
theorem certificate9220 : thCheck pres.relatorLetters = true :=
  CFSG.KC.Th.Soundness.surj_sound CFSG.Sporadic.Bridge.Th.pres CFSG.KC.Th.Soundness.isHsw_pres
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CFSG.KD.ThSj.LI_eq CFSG.KD.ThSj.LS_eq
    CFSG.KD.ThSeed.LA_eq CFSG.KD.ThSeed.LB_eq CFSG.KD.ThS.k0 CFSG.KD.ThSeed.dA CFSG.KD.ThSeed.dB
    CFSG.KC.Th.SurjK.text CFSG.KC.Th.SurjK.regs CFSG.KC.Th.SurjK.rels CFSG.KC.Th.SurjK.words
    CFSG.KC.Th.SurjK.std0 CFSG.KC.Th.SurjK.std1

end Certificates
