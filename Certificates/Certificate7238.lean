module

public import CFSG.Quasithin.Background.HFCodeInputs
public import CFSG.Quasithin.Background.HF22Inputs
import Certificates.Kernel.HMathieu.Odd
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu.Odd

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
public theorem certificate7238 :
    (
      oddFixOK 10 4 T22s3 matsC22s3 ∧ oddFixOK 10 4 T22s5 matsC22s5 ∧
        oddFixOK 10 4 T22s7 matsC22s7 ∧ oddFixOK 10 4 T22s11 matsC22s11) ∧ h1607Check22 := by
  have h10 : oddOK κC22Cols lift22Cols 10 6 16 (G.getD 10 []) (E.getD 10 []) (J.getD 10 []) =
    true := oddK10
  have h11 : oddOK κC22Cols lift22Cols 10 7 16 (G.getD 11 []) (E.getD 11 []) (J.getD 11 []) =
    true := oddK11
  have h12 : oddOK κC22Cols lift22Cols 10 7 16 (G.getD 12 []) (E.getD 12 []) (J.getD 12 []) =
    true := oddK12
  have h13 : oddOK κC22Cols lift22Cols 10 7 16 (G.getD 13 []) (E.getD 13 []) (J.getD 13 []) =
    true := oddK13
  have t3 : T22s3 = PT.ofGens 24 ((G.getD 10 []).map unpk) 16 := by unfold T22s3; congr 1
  refine ⟨?_, ?_⟩
  · exact ⟨oddFix_of t3 h10 le_rfl rfl,
      oddFix_of (by unfold T22s5; congr 1) h11 (by norm_num) rfl,
      oddFix_of (by unfold T22s7; congr 1) h12 (by norm_num) rfl,
      oddFix_of (by unfold T22s11; congr 1) h13 (by norm_num) rfl⟩
  intro s hs
  have hok := tail_of t3 h10 h22 (k := 4) (by norm_num) s hs
  unfold okH22 at hok
  obtain ⟨h, hh, hb⟩ := List.any_eq_true.1 hok
  simp only [Bool.and_eq_true] at hb
  exact ⟨h, hh, hb.1.1, hb.1.2, hb.2⟩

end Certificates
