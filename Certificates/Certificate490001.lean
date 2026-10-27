module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C490001
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.Pred24Sound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14 CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace CertificateChecks.Batch490001

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14 CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

theorem all_mask {l : List T24s2.Elem} (hl : IsCommInvol l)
    (f : Array Nat → Bool) :
    ((subprods l).all fun x => f (T24s2.arr x)) =
      ((subprods l).map inv24s2.idxOf).all (maskOf 192 fun k => f (unpk (T24.P.getD k 0))).testBit := by
  rw [List.all_map]
  refine all_congr_mem fun x hx => ?_
  have hS := mem_or_one_of_subprods T24.gtabs hl hx
  have hk : inv24s2.idxOf x < 192 := by
    have := idxOf_le (R := inv24s2) x
    rw [T24.len] at this
    omega
  simp only [Function.comp_apply]
  rw [testBit_maskOf 192 _ hk, arr_eq T24.packed, show inv24s2 = T24s2.invols from rfl,
    pk_idxOf T24.packed T24.invData hS]

end CertificateChecks.Batch490001

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14 in
theorem certificate490001 :
    forallGreedyAll pos24s2 inv24s2 predC1 7 [] = true := by
  refine forallGreedyAll_matsL T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Mc
    predC1 (fun L S _ => predC1K C490001.mS C490001.mT C490001.mF L S) (fun l hl hind => ?_) 7
    (by rw [T24.len]; exact C490001.search)
  have hci := isCommInvol_of_indepList hind
  have hF : (c1Fuse.any fun cs => (subprods l).all fun x =>
      inTab64 (if cs.2 then tabS else tabT) (c1Conj cs.1 (T24s2.arr x))) =
      C490001.mF.any fun mf => ((subprods l).map inv24s2.idxOf).all mf.testBit := by
    rw [← C490001.maskF, c1MaskF, List.any_map]
    refine Bool.eq_iff_iff.2 (by
      simp only [List.any_eq_true, Function.comp_apply]
      refine exists_congr fun cs => and_congr_right fun _ => ?_
      rw [← Bool.eq_iff_iff.1 rfl]
      simp only [c1Conj_eq]
      rw [CertificateChecks.Batch490001.all_mask hci (fun a => inTab64 (if cs.2 then tabS else tabT) (c1ConjL cs.1 a))])
  unfold predC1 predC1K
  rw [hF, CertificateChecks.Batch490001.all_mask hci (inTab64 tabS), CertificateChecks.Batch490001.all_mask hci (inTab64 tabT),
    ← c1MaskS, ← c1MaskT, C490001.maskS, C490001.maskT, List.length_map]

end Certificates
