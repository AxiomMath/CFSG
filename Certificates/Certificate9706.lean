module

public import CFSG.LieType.SeitzGeneration.HeisSmallData8
import CFSG.Certificates.Kernel.OuterNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.Q8

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9706 : heisCheck 8 QExt.omega gens8 words1_8 words2_8 = true := by
  have hw : words2_8 = decodeL KernelHeis.W8.chars := by
    rw [KernelHeis.W8.eq, decodeWords_ofList]
  have hg : gens8 = (rawGens8.map matN).map (FK.toL fk8 GF8.ofNat') := by
    rw [gens8, List.map_map]
    rfl
  have ho : (QExt.omega : Q8) = FK.dec fk8 GF8.ofNat' 8 := by
    ext <;> rfl
  rw [hw, hg, ho]
  exact FK.heisN_sound fk8_sound 8 8 rawGens8 words1_8 _ KernelHeis.heis8_k

end Certificates
