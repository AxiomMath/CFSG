module

public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitInputs
import Certificates.Kernel.IdxFour.Orbit

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17641 : ∀ U : Submodule (ZMod 2) V12, (∀ s ∈ E0, s (vecOf 15) = vecOf 15 → ∀ u ∈ U, s u ∈ U) →
    4 < Nat.card U → ∃ w ∈ U, Orb.inO378b (codeOf w) = true :=
  fun _ hinv hcard => CFSG.KD.IF4O.sub6
    (fun s hs u hu => hinv s (mem_stabIn.1 hs).1 (mem_stabIn.1 hs).2 u hu) hcard

end Certificates
