module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C490031
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
theorem certificate490031 :
    forallGreedyAll pos24s2 inv24s2 predH165 6 [] = true := by
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Md 11
    predH165 (predH165K T24.E T24.P) (fun l hl hind => ?_) 6
    (by rw [T24.len]; exact C490031.search)
  have hci := isCommInvol_of_indepList hind
  have hn := normalChainB_eq T24.packed T24.invData T24.idOK hci hl
  have hR : inv24s2 = T24s2.invols := rfl
  have hks : ((subprods l).all fun x => ksRefArrs.contains (T24s2.arr x)) =
      ((subprods l).map inv24s2.idxOf).all fun s => ksRefArrs.contains (unpk (T24.P.getD s 0)) := by
    rw [List.all_map]
    refine all_congr_mem fun x hx => ?_
    simp only [Function.comp_apply]
    rw [arr_eq T24.packed, hR, pk_idxOf T24.packed T24.invData
      (mem_or_one_of_subprods T24.gtabs hci hx)]
  unfold predH165 predHF24 predH165K predHF24K fixSt
  rw [hks, T24.codeFixMasks_eq hci.1, fixMasks_map 11 (fun x => T24.Md.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.codeAct_mem (hl x hx)), List.length_map, hn]
  simp only [hR]

end Certificates
