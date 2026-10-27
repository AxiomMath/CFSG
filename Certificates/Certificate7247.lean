module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C7247
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace CertificateChecks.Batch7247

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

theorem presUT : t24PresUT = true := by
  have h := C7247.presUT
  unfold t24PresUTK at h
  rw [all_E T24.packed] at h
  unfold t24PresUT
  rw [← h]
  refine all_congr_mem fun i _ => all_congr_mem fun m hm => ?_
  have hlt : ∀ m ∈ uTMasks, m < 2 ^ 11 := by decide
  rw [T24.act_pk _ (hlt m hm)]

theorem fix : t24Fix = true := by
  have h := C7247.fix
  unfold t24FixK at h
  have e : ((List.range (2 ^ 11)).filter fun m => (List.finRange T24s2.n).all fun i =>
        act24s2 (T24s2.elemEquiv.symm i) m == m) =
      (List.range (2 ^ 11)).filter fun m => T24.E.all fun e =>
        CFSG.KC.HMathieu.actP CFSG.Quasithin.H.Mathieu.ccECols
          CFSG.Quasithin.H.Mathieu.liftECols e m == m := by
    refine List.filter_congr fun m hm => ?_
    rw [all_E T24.packed]
    refine all_congr_mem fun i _ => ?_
    rw [T24.act_pk _ (List.mem_range.1 hm)]
  unfold t24Fix
  rw [e]
  exact h

end CertificateChecks.Batch7247

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 in
theorem certificate7247 : 
    forallGreedyAll pos24s2 inv24s2 predKT 6 [] = true ∧ t24PresUT = true ∧ t24Fix = true := by
  refine ⟨?_, CertificateChecks.Batch7247.presUT, CertificateChecks.Batch7247.fix⟩
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Mc 11
    predKT (fun _ _ st => predKTK st) (fun l hl hind => ?_) 6
    (by rw [T24.len]; exact C7247.search)
  have hci := isCommInvol_of_indepList hind
  unfold predKT predKTK fixSt
  rw [fixMasks24_eq hci.1, fixMasks_map 11 (fun x => T24.Mc.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.act_mem (hl x hx)), List.length_map]

end Certificates
