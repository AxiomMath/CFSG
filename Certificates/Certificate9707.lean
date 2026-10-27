module

public import CFSG.LieType.SeitzGeneration.HeisSmallData11
import CFSG.Certificates.Kernel.HeisNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.C9707

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9707 : heisCheck 11 QExt.omega gens11 words1_11 words2_11 = true := by
  have hw : words2_11 = decodeL KernelHeis.W11.chars := by
    rw [KernelHeis.W11.eq, decodeWords_ofList]
  have hg : gens11 = (rawGens11.map matN).map (FK.toL (fkP 11) (fun n : ℕ => (n : ZMod 11))) := by
    rw [gens11, List.map_map]
    rfl
  have ho : (QExt.omega : Q11) = FK.dec (fkP 11) (fun n : ℕ => (n : ZMod 11)) 11 := by
    ext <;> rfl
  rw [hw, hg, ho]
  exact FK.heisN_sound (fkP_sound 11) 11 11 rawGens11 words1_11 _ KernelHeis.heis11_k

end Certificates
