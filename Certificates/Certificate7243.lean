module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C7243
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
theorem certificate7243 :
    forallGreedyAll pos24s2 inv24s2 predHF24 6 [] = true := by
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Md 11
    predHF24 (predHF24K T24.E T24.P) (fun l hl hind => ?_) 6
    (by rw [T24.len]; exact C7243.search)
  have hci := isCommInvol_of_indepList hind
  have hn := normalChainB_eq T24.packed T24.invData T24.idOK hci hl
  unfold predHF24 predHF24K fixSt
  rw [T24.codeFixMasks_eq hci.1, fixMasks_map 11 (fun x => T24.Md.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.codeAct_mem (hl x hx)), List.length_map]
  have hR : inv24s2 = T24s2.invols := rfl
  rw [hn]
  simp only [hR]

end Certificates
