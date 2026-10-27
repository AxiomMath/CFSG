
module

public import CFSG.Quasithin.Background.E2TwoProofSporJ2KInputs
import Certificates.Kernel.J2Dc.LatD

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.E2P.SporB.J2Lat in
theorem certificate7125 : 
    LatFactsK (codeSetLab 315) 315 j2ta.toArray j2tb.toArray j2Delta
      (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J) (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J)
      CFSG.Quasithin.E2P.SporB.j2Sg j2STabs j2LatD ∧
    j2LatD.Om.map (fun o => o.lbl.size) = #[1, 3, 9, 15, 3] :=
  CFSG.KD.J2Dc.j2D_facts

end Certificates
