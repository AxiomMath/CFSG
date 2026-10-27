module

public import Certificates.Data.E68Spor.Chk
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
import Certificates.Kernel.E68Spor4213.Orb
import Certificates.Kernel.E68Spor4213.R
import CFSG.Certificates.Kernel.E68SporClassSound
import CFSG.Certificates.Kernel.SporLatCodeRSound

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KC.SLOrb CFSG.KC.SLOm CFSG.KD.E68S4213

open CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat in
theorem certificate4213 :
    (classChk 23 m23ta.toArray m23tb.toArray m23SLP[159]! 3795 = true ∧
      rChk 23 (codeSetAct 23) CFSG.Quasithin.H.MathieuLat.m23Delta
        CFSG.Quasithin.H.MathieuLat.m23STabs m23ta.toArray m23tb.toArray m23SLP[159]!
        m23UWords m23YWord m23NWord 7 21 = true) ∧
    (classChk 24 m24ta.toArray m24tb.toArray m24SLP[162]! 11385 = true ∧
      rChk 24 (codeSetAct 24) CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Delta
        CFSG.QuasithinUnique.Ch1.SporLat.M24.m24STabs m24ta.toArray m24tb.toArray m24SLP[162]!
        m24UWords m24YWord m24NWord 7 21 = true) := by
  have t23 := tab23
  have t24 := tab24
  have g23 := good23
  have g24 := good24
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at t23 t24 g23 g24
  obtain ⟨⟨⟨a23, b23⟩, z23⟩, s23⟩ := g23
  obtain ⟨⟨⟨a24, b24⟩, z24⟩, s24⟩ := g24
  have e23 : CFSG.Quasithin.H.MathieuLat.m23Delta = D23 := by
    rw [CFSG.Quasithin.H.MathieuLat.m23Delta, CFSG.KC.E64F.sortN_eq]
    rfl
  have e24 : CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Delta = D24 := by
    rw [CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Delta, CFSG.KC.E64F.sortN_eq]
    rfl
  rw [e23, e24]
  exact ⟨⟨classChk_of_tab (by decide) t23.1 t23.2 orb23,
      rChkC_sound (fun l hl => good_of_goodB (s23 l hl)) (good_of_goodB a23) (good_of_goodB b23)
        (good_of_goodB z23) r23⟩,
    ⟨classChk_of_tab (by decide) t24.1 t24.2 orb24,
      rChkC_sound (fun l hl => good_of_goodB (s24 l hl)) (good_of_goodB a24) (good_of_goodB b24)
        (good_of_goodB z24) r24⟩⟩

end Certificates
