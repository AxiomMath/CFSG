module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Quasithin.Background.HSporLatM12Sg
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatFactsK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
import Certificates.Certificate3086
import Certificates.Certificate4075
import Certificates.Kernel.M12Dc.Final
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat in
theorem certificate7116 :
    ∃ D : LatData (List ℕ),
      LatFactsK (codeSetLab 12) 12 m12ta.toArray m12tb.toArray m12Delta
        CFSG.Sporadic.Mathieu.m12a CFSG.Sporadic.Mathieu.m12b CFSG.Quasithin.H.MathieuLat.m12Sg m12STabs D ∧
      D.Om.map (fun o => o.lbl.size) = #[1, 3, 3] :=
  ⟨CFSG.KD.M12Dc.m12LatK, ⟨rfl, CFSG.KD.M12Dc.m12K_membersOK, CFSG.KD.M12Dc.m12K_stab,
    CFSG.KD.M12Dc.m12K_comp⟩, CFSG.KD.M12Dc.m12K_Om_size⟩

end Certificates
