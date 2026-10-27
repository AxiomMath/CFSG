module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Quasithin.Background.HSporLatM23Sg
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import Certificates.Certificate2197
import Certificates.Certificate4075
import Certificates.Kernel.M23Dc.Facts

public section

namespace Certificates

open CFSG.KD.M23Dc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat in
theorem certificate7118 :
    ∃ D : LatData (List ℕ),
      LatFactsK (codeSetLab 23) 23 m23ta.toArray m23tb.toArray m23Delta
        CFSG.Sporadic.Schreier.m23GenA CFSG.Sporadic.Schreier.m23GenB CFSG.Quasithin.H.MathieuLat.m23Sg m23STabs D ∧
      D.Om.map (fun o => o.lbl.size) =
        #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] ∧
      D.mw = CFSG.Quasithin.A312M23.m23MwLit := by
  refine ⟨m23LatK, ⟨rfl, m23K_membersOK, ?_, ?_⟩, m23K_Om_size, m23K_mw_eq⟩
  · rw [← m23Sg_eq_lat]
    exact m23K_stab
  · rw [← m23Sg_eq_lat]
    exact m23K_comp

end Certificates
