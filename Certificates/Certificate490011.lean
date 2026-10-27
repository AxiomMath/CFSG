module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C490011
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH in
theorem certificate490011 :
    forallGreedyAll pos24s2 inv24s2 predOff24 7 [] = true := by
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Mc 11
    predOff24 (fun L _ st => predOff24K T24.P L st) (fun l hl hind => ?_) 7
    (by rw [T24.len]; exact C490011.search)
  have hci := isCommInvol_of_indepList hind
  have hfix : l.all fixesOff24 = (l.map inv24s2.idxOf).all fun a =>
      offPts24.all fun i => CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) (T24.P.getD a 0) i == i := by
    rw [List.all_map]
    refine all_congr_mem fun x hx => all_congr_mem fun i hi => ?_
    have hlt : ∀ i ∈ offPts24, i < 24 := by decide
    have hi' := hlt i hi
    simp only [Function.comp_apply]
    rw [T24.arr_get x hi', show inv24s2 = T24s2.invols from rfl,
      pk_idxOf T24.packed T24.invData (Or.inl (hl x hx))]
  unfold predOff24 predOff24K fixSt
  rw [hfix, fixMasks24_eq hci.1, fixMasks_map 11 (fun x => T24.Mc.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.act_mem (hl x hx)), List.length_map]

end Certificates
