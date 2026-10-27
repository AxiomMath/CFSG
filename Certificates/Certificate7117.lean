module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Quasithin.Background.HSporLatM22Sg
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import Certificates.Certificate3029
import Certificates.Certificate4075
import Certificates.Kernel.M22Dc.Final
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat in
theorem certificate7117 :
    ∃ D : LatData (List ℕ),
      LatFactsK (codeSetLab 22) 22 m22ta.toArray m22tb.toArray m22Delta
        CFSG.Sporadic.Mathieu.m22a CFSG.Sporadic.Mathieu.m22b CFSG.Quasithin.H.MathieuLat.m22Sg m22STabs D ∧
      D.Om.map (fun o => o.lbl.size) = #[1, 45, 3, 15, 3] := by
  have e : CFSG.KD.M22Dc.m22Sg = CFSG.Quasithin.H.MathieuLat.m22Sg := rfl
  refine ⟨CFSG.KD.M22Dc.m22LatK, ⟨rfl, CFSG.KD.M22Dc.m22K_membersOK, ?_, ?_⟩,
    CFSG.KD.M22Dc.m22K_Om_size⟩
  · rw [← e]
    exact CFSG.KD.M22Dc.m22K_stab
  · rw [← e]
    exact CFSG.KD.M22Dc.m22K_comp

end Certificates
