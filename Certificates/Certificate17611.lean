module

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import CFSG.GF2Type.Smith1979.IdxFourModelData
import Certificates.Kernel.IdxFour.Sift

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17611 : (∀ l ∈ Viol.genGrp lbarGens, ∀ e ∈ E0, l * e * l⁻¹ ∈ E0) ∧
    (∀ l ∈ Viol.genGrp lbarGens, l * omegaE = omegaE * l → l ∈ E0) ∧
    Viol.genGrp skGens ≤ E0 ⊔ Viol.genGrp lbarGens ∧ s12e ∉ E0 ⊔ Viol.genGrp lbarGens :=
  CFSG.KD.IF4R.sift17611

end Certificates
