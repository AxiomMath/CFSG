module

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import CFSG.GF2Type.Smith1979.IdxFourModelData
import Certificates.Kernel.IdxFour.LbarFacts

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17608 :
    Nat.card (Viol.genGrp lbarGens) = 32 ∧
    (∀ l ∈ Viol.genGrp lbarGens, l * l = 1) ∧
    (∀ l ∈ Viol.genGrp lbarGens, ∀ l' ∈ Viol.genGrp lbarGens, l * l' = l' * l) ∧
    (∀ g ∈ Viol.genGrp sGens, ∀ l ∈ Viol.genGrp lbarGens, g * l * g⁻¹ ∈ Viol.genGrp lbarGens) ∧
    Nat.card {t : V12 ≃ₗ[ZMod 2] V12 // t ∈ Viol.genGrp lbarGens ∧ t * omegaE = omegaE * t} = 16 ∧
    (∀ t ∈ Viol.genGrp lbarGens, ∀ t' ∈ Viol.genGrp lbarGens, t ≠ 1 → t' ≠ 1 →
      t * omegaE = omegaE * t → t' * omegaE = omegaE * t' →
      ∃ g ∈ Viol.genGrp sGens, g * t * g⁻¹ = t') ∧
    720 ≤ (Subgroup.centralizer
      {t | t ∈ Viol.genGrp lbarGens ∧ t * omegaE = omegaE * t}).relIndex (Viol.genGrp sGens) ∧
    spanOf vtBasis ≤ Submodule.span (ZMod 2) {y | ∃ l ∈ Viol.genGrp lbarGens, ∃ x : V12,
      f0 x (vecOf 15) = 0 ∧ f0 x (vecOf 960) = 0 ∧ y = l x - x} :=
  CFSG.KD.IF4T.facts17608

end Certificates
