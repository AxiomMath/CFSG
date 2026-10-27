module

public import CFSG.LieType.SeitzGeneration.HeisSmallData5
import CFSG.Certificates.Kernel.HeisNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.C9704

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9704 : heisCheck 5 QExt.omega gens5 words1_5 words2_5 = true := by
  have hw : words2_5 = decodeL KernelHeis.W9704.chars := by
    rw [KernelHeis.W9704.eq, decodeWords_ofList]
  have hg : gens5 = (rawGens5.map matN).map (FK.toL (fkP 5) (fun n : ℕ => (n : ZMod 5))) := by
    rw [gens5, List.map_map]
    rfl
  have ho : (QExt.omega : Q5) = FK.dec (fkP 5) (fun n : ℕ => (n : ZMod 5)) 5 := by
    ext <;> rfl
  rw [hw, hg, ho]
  exact FK.heisN_sound (fkP_sound 5) 5 5 rawGens5 words1_5 _ KernelHeis.heis5_k

end Certificates
