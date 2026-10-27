module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C8282
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H13.Mat CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Mat in
theorem certificate8282 :
    forallGreedyAll pos24s2 inv24s2 predMB24 6 [] = true := by
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Mc 11
    predMB24 (fun _ _ st => predMB24K st) (fun l hl hind => ?_) 6
    (by rw [T24.len]; exact C8282.search)
  have hci := isCommInvol_of_indepList hind
  have hcomm : l.all (chainCommIn24 r4L9) =
      (l.map fun x => T24.Mc.getD (inv24s2.idxOf x) []).all (chainCommInM 11 r4L9) := by
    rw [List.all_map]
    refine all_congr_mem fun x hx => ?_
    unfold chainCommIn24 chainCommInM
    simp only [Function.comp_apply]
    rw [T24.act_mem (hl x hx)]
  unfold predMB24 predMB24K predKT predKTK fixSt
  rw [hcomm, fixMasks24_eq hci.1, fixMasks_map 11 (fun x => T24.Mc.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.act_mem (hl x hx)), List.length_map]

end Certificates
