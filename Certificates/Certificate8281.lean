module

public import Certificates.Kernel.HMathieu.T22Glue
public import Certificates.Kernel.HMathieu.C8281
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Mat CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Mat in
theorem certificate8281 :
    forallGreedyAll pos22s2 inv22s2 predMB22 5 [] = true := by
  refine forallGreedyAll_fix T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq T22.Md 10
    predMB22 (fun _ _ st => predMB22K st) (fun l hl hind => ?_) 5
    (by rw [T22.len]; exact C8281.search)
  have hci := isCommInvol_of_indepList hind
  have hc : ∀ B, ∀ x ∈ l,
      chainCommIn B x = chainCommInM 10 B (T22.Md.getD (inv22s2.idxOf x) []) := by
    intro B x hx
    unfold chainCommIn chainCommInM
    rw [T22.codeAct_mem (hl x hx)]
  have h1 : l.all (chainCommIn r2B9) =
      (l.map fun x => T22.Md.getD (inv22s2.idxOf x) []).all (chainCommInM 10 r2B9) := by
    rw [List.all_map]
    exact all_congr_mem fun x hx => hc r2B9 x hx
  have h2 : (l.any fun s => !(chainCommIn r2W8 s)) =
      (l.map fun x => T22.Md.getD (inv22s2.idxOf x) []).any fun M => !(chainCommInM 10 r2W8 M) := by
    rw [List.any_map, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    refine exists_congr fun x => and_congr_right fun hx => ?_
    simp only [Function.comp_apply]
    rw [hc r2W8 x hx]
  unfold predMB22 predU22 predMB22K fixSt
  rw [h1, h2, T22.codeFixMasks_eq hci.1, fixMasks_map 10
    (fun x => T22.Md.getD (inv22s2.idxOf x) []) (fun x hx => T22.codeAct_mem (hl x hx)),
    List.length_map]

end Certificates
