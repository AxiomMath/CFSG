module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11Inputs
import Certificates.Kernel.LocalQT.Lat.C4084
import CFSG.Certificates.Kernel.LocalQTContainsCSound
import CFSG.Certificates.Kernel.LocalQTDiagKSound

public section

namespace Certificates

open CFSG.KD.LQT.C4084 CFSG.QuasithinUnique.Vol2Native.A312L.M11Lat in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M11Lat in
open Equiv PermLat in
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot in
theorem certificate4084 : (cert.check RN.enc = true)
    ∧ (diagOK (RN.enc : Perm (Fin 11) → RN 11) (RN.enc : Perm (Fin 6) → RN 6) 64
          aGens a6Gens 360 = true)
    ∧ ((List.range 5).all (fun j => cert.sizes.getD j 0 != 720 ||
          aGens.all fun g => (elts (RN.enc : Perm (Fin 11) → RN 11) 64
            ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true) :=
  ⟨CFSG.KC.LQT.CM.latC_sound (by decide) C CFSG.KD.LQT.C4084.inj MW ms cert hl,
    CFSG.KC.LQT.CM.diag_sound (by decide) (by decide) aGens a6Gens hd,
    CFSG.KC.LQT.CM.containsC_sound (by decide) C CFSG.KD.LQT.C4084.inj ms cert aGens hc⟩

end Certificates
