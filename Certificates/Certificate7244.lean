module

public import CFSG.Quasithin.Background.HFCodeInputs
import Certificates.Kernel.HMathieu.Odd
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu.Odd

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
public theorem certificate7244 :
    
      (∀ p : T24s3.Elem, p * p * p = 1) ∧ oddFixOK 11 5 T24s3 matsC24s3 ∧
        oddFixOK 11 4 T24s5 matsC24s5 ∧ oddFixOK 11 4 T24s7 matsC24s7 ∧
        oddFixOK 11 4 T24s11 matsC24s11 ∧ oddFixOK 11 4 T24s23 matsC24s23 := by
  have h5 : oddOK κCCols liftCCols 11 6 32 (G.getD 5 []) (E.getD 5 []) (J.getD 5 []) = true := oddK5
  have h6 : oddOK κCCols liftCCols 11 7 16 (G.getD 6 []) (E.getD 6 []) (J.getD 6 []) = true := oddK6
  have h7 : oddOK κCCols liftCCols 11 7 16 (G.getD 7 []) (E.getD 7 []) (J.getD 7 []) = true := oddK7
  have h8 : oddOK κCCols liftCCols 11 7 16 (G.getD 8 []) (E.getD 8 []) (J.getD 8 []) = true := oddK8
  have h9 : oddOK κCCols liftCCols 11 7 32 (G.getD 9 []) (E.getD 9 []) (J.getD 9 []) = true := oddK9
  have t3 : T24s3 = PT.ofGens 24 ((G.getD 5 []).map unpk) 32 := by unfold T24s3; congr 1
  exact ⟨cube_of (packed_of_oddOK t3 h5) cube, oddFix_of t3 h5 le_rfl rfl,
    oddFix_of (by unfold T24s5; congr 1) h6 le_rfl rfl,
    oddFix_of (by unfold T24s7; congr 1) h7 le_rfl rfl,
    oddFix_of (by unfold T24s11; congr 1) h8 le_rfl rfl,
    oddFix_of (by unfold T24s23; congr 1) h9 le_rfl rfl⟩

end Certificates
