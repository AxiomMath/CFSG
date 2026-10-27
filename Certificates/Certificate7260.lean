module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C7260
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.OrbSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24 CFSG.KC.HMathieu
open CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24 in
theorem certificate7260 : 
    forallGreedyAll pos24s2 inv24s2 predKS 6 [] = true ∧
      orbCheck 11 [codColsA, codColsB] uSBasis 1771 = true ∧
      orbCheck 11 [cocColsA, cocColsB] uTBasis' 3795 = true := by
  refine ⟨?_, orbCheck_of (by decide) (by decide) C7260.orbS,
    orbCheck_of (by decide) (by decide) C7260.orbT⟩
  refine forallGreedyAll_fix T24.gtabs (by rw [T24.len]; exact T24.lenOK.2) pos24s2_eq T24.Md 11
    predKS (fun _ _ st => predKSK st) (fun l hl hind => ?_) 6
    (by rw [T24.len]; exact C7260.search)
  have hci := isCommInvol_of_indepList hind
  unfold predKS predKSK fixSt
  rw [T24.codeFixMasks_eq hci.1, fixMasks_map 11 (fun x => T24.Md.getD (inv24s2.idxOf x) [])
    (fun x hx => T24.codeAct_mem (hl x hx)), List.length_map]

end Certificates
