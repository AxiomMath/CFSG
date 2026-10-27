module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2LatInputs
import Certificates.Certificate3139
import Certificates.Certificate4142
import Certificates.Kernel.AutJ2Lat.Final

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.ComponentClassification.J2Cover CFSG.Quasithin.F112R.AJ2L in
theorem certificate40702 : 
    Subgroup.closure ({CFSG.Quasithin.F112R.AJ2L.xR, yR} : Set R) = ⊤ ∧
    LatFactsK (codeSetLab 315) 315 (tab 315 CFSG.Quasithin.F112R.AJ2L.xR).toArray (tab 315 yR).toArray rDelta CFSG.Quasithin.F112R.AJ2L.xR yR rSg
      (genTabs 315 rSg) rLatD ∧
    rLatD.Om.map (fun o => o.lbl.size) = #[1, 9, 15, 3, 3] ∧
    O2OK (codeSetAct 315) rLatD rOtD ∧ (List.range 5).map (defaultRow 8 rLatD rOtD) = CFSG.Quasithin.F112R.AJ2L.mems ∧
    GensIn (codeSetAct 315) rDelta rLatD 3 1 ∧ GensIn (codeSetAct 315) rDelta rLatD 4 1 ∧
    GensIn (codeSetAct 315) rDelta rLatD 4 2 :=
  CFSG.KD.AutJ2Lat.stmt40702

end Certificates
