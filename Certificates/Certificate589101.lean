module

public import Certificates.Kernel.S1277.NmFacts
public import CFSG.Certificates.Kernel.S1277KMLSound

public section

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KD.S1277Gm CFSG.KC.S1277ML
  CFSG.KP.S1277ML CFSG.KS.S1277ML

theorem orbitSize_iff_m18_m45 (c : ℕ) (hc : c < 64) :
    (Certificates.Data.S1277MLine.orbitSize gm6 c = 18 ↔ bitN m18M c = true) ∧
      (Certificates.Data.S1277MLine.orbitSize gm6 c = 45 ↔ bitN m45M c = true) := by
  rw [CFSG.KP.S1277Gm.gm6_eq]
  exact osChk_sound gm6P m18M m45M os_ok c hc

theorem certificate589101 :
    (Certificates.Data.S1277MLine.mCheck CFSG.Quasithin.H13.S127.Mod.gm6 () = true)
    ∧ (Certificates.Data.S1277MLine.mCheck CFSG.Quasithin.H13.S127.Mod.nm6 () = true) :=
  ⟨by
      rw [CFSG.KP.S1277Gm.gm6_eq]
      exact mChk_sound _ m18M m45M (fun c hc => (orbitSize_iff_m18_m45 c hc).1)
        (fun c hc => (orbitSize_iff_m18_m45 c hc).2) mchk_gm,
    by
      rw [nm6_eqP]
      exact mChk_sound _ m18M m45M (fun c hc => (orbitSize_iff_m18_m45 c hc).1)
        (fun c hc => (orbitSize_iff_m18_m45 c hc).2) mchk_nm⟩

end Certificates
