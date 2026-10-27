
module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
import Certificates.Kernel.IdxFour.OrbitM0

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17603 :
    (∀ U ∈ M0, ∀ v : V12, Orb.inO378b (codeOf v) = true → Orb.inO378b (codeOf (U v)) = true) ∧
    (∀ U ∈ M0, ∀ v : V12, Orb.inO1701b (codeOf v) = true →
      Orb.inO1701b (codeOf (U v)) = true) ∧
    (∀ v : V12, Orb.inO378b (codeOf v) = true → ∃ U ∈ E0, U (vecOf 3) = v) ∧
    (∀ v : V12, Orb.inO1701b (codeOf v) = true → ∃ U ∈ E0, U (vecOf 15) = v) :=
  CFSG.KD.IF4O.orbit_facts

end Certificates
