module

public import CFSG.LieType.SeitzGeneration.OuterSmallData8
import CFSG.Certificates.Kernel.OuterNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.Q8

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9709 : outerCheck 8 QExt.omega outerLetters8 words2_8 outerTable8 = true := by
  have hw : words2_8 = decodeL KernelHeis.W8.chars := by
    rw [KernelHeis.W8.eq, decodeWords_ofList]
  have hl : outerLetters8 =
      words1_8.map (evalW (rawGens8.map fun l => FK.toL fk8 GF8.ofNat' (matN l))) := rfl
  have ht : outerTable8 = outerRaw8.map fun r =>
      (⟨FK.dec fk8 GF8.ofNat' r.1, r.2.1.map fun l => FK.toL fk8 GF8.ofNat' (matN l), r.2.2⟩ :
        OuterEntry Q8) := rfl
  have ho : (QExt.omega : Q8) = FK.dec fk8 GF8.ofNat' 8 := by
    ext <;> rfl
  rw [hw, hl, ht, ho]
  exact FK.outerN_sound fk8_sound 8 8 rawGens8 words1_8 _ outerRaw8 KernelHeis.outer8_k

end Certificates
