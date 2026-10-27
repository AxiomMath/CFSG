module

public import Certificates.Kernel.HMathieu.T22Glue
public import Certificates.Kernel.HMathieu.C7225
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
theorem certificate7225 :
    forallGreedyAll pos22s2 inv22s2 predHF22 5 [] = true := by
  refine forallGreedyAll_fix T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq T22.Md 10
    predHF22 (predHF22K T22.E T22.P) (fun l hl hind => ?_) 5
    (by rw [T22.len]; exact C7225.search)
  have hci := isCommInvol_of_indepList hind
  have hn := normalChainB_eq T22.packed T22.invData T22.idOK hci hl
  unfold predHF22 predHF22K fixSt
  rw [T22.codeFixMasks_eq hci.1, fixMasks_map 10 (fun x => T22.Md.getD (inv22s2.idxOf x) [])
    (fun x hx => T22.codeAct_mem (hl x hx)), List.length_map]
  have hR : inv22s2 = T22s2.invols := rfl
  rw [hn]
  simp only [hR]

end Certificates
