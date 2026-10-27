module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
public import CFSG.GF2Type.Smith1979.IdxFourModelData
import Certificates.Kernel.IdxFour.SkChain

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17612 : Nat.card (Viol.genGrp skGens) = 256 ∧
    ∀ s ∈ Viol.genGrp skGens, s * s = 1 → ∃ h ∈ M0, h * s * h⁻¹ ∈ Viol.genGrp lbarGens :=
  ⟨CFSG.KD.IF4K.card_S, CFSG.KD.IF4K.conj_S⟩

end Certificates
