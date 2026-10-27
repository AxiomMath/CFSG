module

public import CFSG.Quasithin.Background.HF22QInputs
public import Certificates.Kernel.HMathieu.T22Glue
public import Certificates.Kernel.HMathieu.C7240
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat in
theorem certificate7240 : 
    forallGreedyAll pos22s2 inv22s2 predQ22in 5 [] = true := by
  refine forallGreedyAll_matsL T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq T22.Md
    predQ22in (fun L _ Ms => predQ22inK T22.P L Ms) (fun l hl hind => ?_) 5
    (by rw [T22.len]; exact C7240.search)
  have hin : l.all inM22s2 = (l.map inv22s2.idxOf).all fun a =>
      CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) (T22.P.getD a 0) 0 == 0 := by
    rw [List.all_map]
    refine all_congr_mem fun x hx => ?_
    simp only [Function.comp_apply]
    unfold inM22s2
    rw [T22.arr_get x (by norm_num), show inv22s2 = T22s2.invols from rfl,
      pk_idxOf T22.packed T22.invData (Or.inl (hl x hx))]
  unfold predQ22in predQ22inK
  rw [hin, predQ_map (act := actC22s2) 10 (fun x => T22.Md.getD (inv22s2.idxOf x) []) true
    (fun x hx => T22.codeAct_mem (hl x hx))]

end Certificates
