module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22DataInputs
import Certificates.Kernel.LocalQT.Lat.C4053
import CFSG.Certificates.Kernel.LocalQTDiagExtSound
import CFSG.Certificates.Kernel.LocalQTLatSixCSound

public section

namespace Certificates

open CFSG.KD.LQT.C4053 CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat in
open Equiv PermLat in
theorem certificate4053 : (cert.check RN.enc = true)
    ∧ (diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 5) → RN 5) 64
          p5Gens a5Gens 960 60 = true)
    ∧ (diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 6) → RN 6) 64
          l6Gens a6Gens 5760 360 = true)
    ∧ (perfOK (RN.enc : Perm (Fin 22) → RN 22) p5Gens perf5 = true)
    ∧ (perfOK (RN.enc : Perm (Fin 22) → RN 22) l6Gens perf6 = true)
    ∧ ((List.range 6).all (fun j => cert.sizes.getD j 0 != 1920 ||
          p5Gens.all fun g => (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.elts (RN.enc : Perm (Fin 22) → RN 22) 64
            ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true)
    ∧ ((List.range 6).all (fun j => cert.sizes.getD j 0 != 5760 ||
          l6Gens.all fun g => (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.elts (RN.enc : Perm (Fin 22) → RN 22) 64
            ((cert.tGens :: cert.lat).getD j [])).contains (RN.enc g)) = true) :=
  ⟨CFSG.KC.LQT.CM.latG_sound (by decide) C MW 2 TW 38 ms 3 labT CFSG.KD.LQT.C4053.inj injM cert
      hl,
    CFSG.KC.LQT.CM.diagExtC_sound (by decide) p5Gens a5Gens C5A W5A C5B W5B C5D W5D inj5.1
      inj5.2.1 inj5.2.2 hd5,
    CFSG.KC.LQT.CM.diagExtC_sound (by decide) l6Gens a6Gens C6A W6A C6B W6B C6D W6D inj6.1
      inj6.2.1 inj6.2.2 hd6,
    CFSG.KC.LQT.CM.perf_sound (by decide) p5Gens perf5 hp5,
    CFSG.KC.LQT.CM.perf_sound (by decide) l6Gens perf6 hp6,
    CFSG.KC.LQT.CM.containsG_sound (by decide) ms injM cert p5Gens hc5,
    CFSG.KC.LQT.CM.containsG_sound (by decide) ms injM cert l6Gens hc6⟩

end Certificates
