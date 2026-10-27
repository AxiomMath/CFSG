module

public import CFSG.Quasithin.Background.HF22UInputs
import Certificates.Kernel.HMathieu.T22Glue
import Certificates.Kernel.HMathieu.C7248
import Certificates.Kernel.HMathieu.Odd
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
public theorem certificate7248 :
    
      forallGreedyAll pos22s2 inv22s2 predU22 5 [] = true ∧
        oddFixOK 10 3 T22s5 matsC22s5 ∧ oddFixOK 10 3 T22s7 matsC22s7 ∧
          oddFixOK 10 3 T22s11 matsC22s11 := by
  have h11 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 11 []) (Odd.E.getD 11 [])
    (Odd.J.getD 11 []) = true := Odd.oddK11
  have h12 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 12 []) (Odd.E.getD 12 [])
    (Odd.J.getD 12 []) = true := Odd.oddK12
  have h13 : oddOK κC22Cols lift22Cols 10 7 16 (Odd.G.getD 13 []) (Odd.E.getD 13 [])
    (Odd.J.getD 13 []) = true := Odd.oddK13
  refine ⟨?_, oddFix_of (by unfold T22s5; congr 1) h11 le_rfl rfl,
    oddFix_of (by unfold T22s7; congr 1) h12 le_rfl rfl,
    oddFix_of (by unfold T22s11; congr 1) h13 le_rfl rfl⟩
  refine forallGreedyAll_fix T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq T22.Md 10
    predU22 (fixEqK 5 u22Masks) (fun l hl hind => ?_) 5 (by rw [T22.len]; exact C7248.search)
  have hci := isCommInvol_of_indepList hind
  unfold predU22 fixEqK fixSt
  rw [T22.codeFixMasks_eq hci.1, fixMasks_map 10 (fun x => T22.Md.getD (inv22s2.idxOf x) [])
    (fun x hx => T22.codeAct_mem (hl x hx)), List.length_map]

end Certificates
