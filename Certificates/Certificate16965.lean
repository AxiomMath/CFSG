
module

import Certificates.Kernel.GammaUStepA.ClassGlue
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16965 : ∀ c < 32, ∃ i, (i = 0 ∨ i = 1) ∧ ∃ g ∈ gammaU, g (vecOf a0) = vecOf a0 ∧
    (∀ y, y ∈ spanOf d0 ↔ g y ∈ spanOf d0) ∧
    ∀ l : V12 ≃ₗ[ZMod 2] V12, (∃ r ∈ compOf c, ∀ x, l x = linOfRows r x) ↔
      ∃ r ∈ compOf i, ∀ x, (g⁻¹ * l * g) x = linOfRows r x :=
  CFSG.KD.GUA.class_16965

end Certificates
