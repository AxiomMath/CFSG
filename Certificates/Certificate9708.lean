module

public import CFSG.LieType.SeitzGeneration.OuterSmallData5
import CFSG.Certificates.Kernel.OuterNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.C9708

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9708 : outerCheck 5 QExt.omega outerLetters5 words2_5 outerTable5 = true := by
  have hw : words2_5 = decodeL KernelHeis.W5.chars := by
    rw [KernelHeis.W5.eq, decodeWords_ofList]
  have hl : outerLetters5 = words1_5.map
      (evalW (rawGens5.map fun l => FK.toL (fkP 5) (fun n : ℕ => (n : ZMod 5)) (matN l))) := rfl
  have ht : outerTable5 = outerRaw5.map fun r =>
      (⟨FK.dec (fkP 5) (fun n : ℕ => (n : ZMod 5)) r.1,
        r.2.1.map fun l => FK.toL (fkP 5) (fun n : ℕ => (n : ZMod 5)) (matN l), r.2.2⟩ :
        OuterEntry Q5) := rfl
  have ho : (QExt.omega : Q5) = FK.dec (fkP 5) (fun n : ℕ => (n : ZMod 5)) 5 := by
    ext <;> rfl
  rw [hw, hl, ht, ho]
  exact FK.outerN_sound (fkP_sound 5) 5 5 rawGens5 words1_5 _ outerRaw5 KernelHeis.outer5_k

end Certificates
