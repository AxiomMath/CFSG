module

public import Certificates.Data.E68Spor.Chk
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
import Certificates.Kernel.E68Spor4212.Checks
import CFSG.Certificates.Kernel.E68SporClassSound

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KC.SLOrb CFSG.KD.E68S4212

open CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.K1.SporadicPerm in
theorem certificate4212 : classChk 11 m11ta.toArray m11tb.toArray m11SLP[159]! 165 = true ∧
    classChk 12 m12ta.toArray m12tb.toArray m12SLP[153]! 495 = true ∧
    classChk 22 m22ta.toArray m22tb.toArray m22SLP[163]! 1155 = true := by
  have t11 := tab11
  have t12 := tab12
  have t22 := tab22
  simp only [Bool.and_eq_true] at t11 t12 t22
  exact ⟨classChk_of_tab (by decide) t11.1 t11.2 orb11, classChk_of_tab (by decide) t12.1 t12.2 orb12,
    classChk_of_tab (by decide) t22.1 t22.2 orb22⟩

end Certificates
