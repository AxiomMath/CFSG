
module

public import Certificates.Certificate7075Base

public import Certificates.Kernel.HMathieu.C7075
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.AvoidSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
theorem certificate7075 :
    forallGreedyAll pos24s2 inv24s2 pred24 7 [] = true := by
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Mc 11
    pred24 (pred24K T24.Mc) (fun l hl hind => ?_) 7 (by rw [T24.len]; exact C7075.search)
  have hci := isCommInvol_of_indepList hind
  unfold pred24 pred24K fixSt xiCheck
  rw [CertificateChecks.Batch7075.xiCands_eq hci, fixMasks24_eq hci.1, fixMasks_map 11
    (fun x => T24.Mc.getD (inv24s2.idxOf x) []) (fun x hx => T24.act_mem (hl x hx)),
    List.length_map]
  simp only [avoidOK_eq]

end Certificates
