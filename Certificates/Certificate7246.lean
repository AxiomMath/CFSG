module

public import CFSG.Quasithin.Background.HF166Inputs
import Certificates.Kernel.HMathieu.Odd24
import CFSG.Certificates.Kernel.HMathieu.OddSound
import CFSG.Certificates.Kernel.HMathieu.PickJSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu.Odd

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
public theorem certificate7246 : h166Check := by
  have h5 : oddOK κCCols liftCCols 11 6 32 (G.getD 5 []) (E.getD 5 []) (J.getD 5 []) = true := oddK5
  have t3 : T24s3 = PT.ofGens 24 ((G.getD 5 []).map unpk) 32 := by unfold T24s3; congr 1
  intro s hs
  have hok := tail_of t3 h5 h24 (k := 5) (by norm_num) s hs
  unfold okH24 at hok
  rcases Bool.or_eq_true_iff.1 hok with hc | hr
  · obtain ⟨h, hh, hb⟩ := List.any_eq_true.1 hc
    simp only [Bool.and_eq_true] at hb
    exact ⟨h, hh, hb.2, hb.1⟩
  · have hl := rankOK_matOf (f := actC11 (T24s3.arr s))
      (((actM_xor _).comp (actM_xor _)).comp (actM_xor _)) hr
    unfold codeFixArr at hs
    rw [hs] at hl
    norm_num at hl

end Certificates
