module

public import Certificates.Kernel.Co1Surj.Checks
public import Certificates.Kernel.Co1M.Orb98280
public import CFSG.Certificates.Kernel.SurjKChainSound
public import CFSG.Certificates.Kernel.SurjKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Surj

open CFSG.KC.SurjK CFSG.KC.SurjChain CFSG.KC.M1F2 CFSG.KC.VecK
open CFSG.KS (lget)
open CFSG.Sporadic.Bridge.SurjD.Native CertificateChecks.KernelVec.Co1 CertificateChecks.KernelCo1M

theorem img_eq : co1Spec.imgWords = Li.toArray := by
  change parseWords co1ImgText = _
  unfold Li
  rw [IT.eq, wordsK_sound kIT]

theorem surj_eq : co1Spec.surjWords = Ls.toArray := by
  change parseWords co1SurjText = _
  unfold Ls
  rw [ST.eq, wordsK_sound kST]

theorem himg (k : Nat) (hk : k < co1Spec.m) :
    wordRF 24 (chainF LM) (Li.getD k []) = lget Ims k := by
  have hL : k < Li.length := by
    have h := kSizes
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    change k < 8 at hk
    omega
  unfold Ims
  rw [lget_eq, List.getD_eq_getElem (List.map _ Li) 0 (by simpa using hL), List.getElem_map,
    List.getD_eq_getElem _ _ hL]

theorem co1Check_k : co1Check () = true := by
  have hs := kSizes
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact chainLetter_sound (CFSG.Sporadic.Co1.Native.co1Data ()) co1Spec
    (NAi := CertificateChecks.KernelVec.Co1.NAi) (NBi := CertificateChecks.KernelVec.Co1.NBi)
    (R := CertificateChecks.KernelVec.Co1.R) (V := CertificateChecks.KernelVec.Co1.V) hA hB cm_seed
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) cmHorb cmHbfs cmHsort
    (by quickRfl) (by quickRfl) (kL := 20) (by quickRfl) (by quickRfl)
    img_eq surj_eq (by rw [hs.1]; rfl) hs.2 kBase himg
    (fun k hk => allN_spec kInv k hk) kRel kSl
    (Nat.eq_of_beq_eq_true kSA) (Nat.eq_of_beq_eq_true kSB)

end CertificateChecks.KernelCo1Surj

end
