module

public import CFSG.LieType.SeitzGeneration.OuterSmallData11
import CFSG.Certificates.Kernel.OuterNSound
import CFSG.Certificates.Kernel.HeisWordsSound
import Certificates.Kernel.Heis.C9710

public section

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.HeisWords

namespace Certificates

open CertificateChecks

open CFSG.LieType.SeitzGeneration.HeisSmall in
theorem certificate9710 : outerCheck 11 QExt.omega outerLetters11 words2_11 outerTable11 = true := by
  have hw : words2_11 = decodeL KernelHeis.W11.chars := by
    rw [KernelHeis.W11.eq, decodeWords_ofList]
  have hl : outerLetters11 = words1_11.map
      (evalW (rawGens11.map fun l => FK.toL (fkP 11) (fun n : ℕ => (n : ZMod 11)) (matN l))) :=
    rfl
  have ht : outerTable11 = outerRaw11.map fun r =>
      (⟨FK.dec (fkP 11) (fun n : ℕ => (n : ZMod 11)) r.1,
        r.2.1.map fun l => FK.toL (fkP 11) (fun n : ℕ => (n : ZMod 11)) (matN l), r.2.2⟩ :
        OuterEntry Q11) := rfl
  have ho : (QExt.omega : Q11) = FK.dec (fkP 11) (fun n : ℕ => (n : ZMod 11)) 11 := by
    ext <;> rfl
  rw [hw, hl, ht, ho]
  exact FK.outerN_sound (fkP_sound 11) 11 11 rawGens11 words1_11 _ outerRaw11
    KernelHeis.outer11_k

end Certificates
