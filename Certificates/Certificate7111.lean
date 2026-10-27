module

public import CFSG.Quasithin.Background.HMathieuCode23Inputs
import Certificates.Kernel.HMathieu.Odd
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu.Odd

namespace Certificates

open CFSG.Quasithin.H.Mathieu in
public theorem certificate7111 :
    
      oddC23OK T23s3 matsC23s3 ∧ oddC23OK T23s5 matsC23s5 ∧ oddC23OK T23s7 matsC23s7 ∧
        oddC23OK T23s11 matsC23s11 ∧ oddC23OK T23s23 matsC23s23 := by
  have h0 : oddOK κCCols liftCCols 11 6 16 (G.getD 0 []) (E.getD 0 []) (J.getD 0 []) = true := oddK0
  have h1 : oddOK κCCols liftCCols 11 6 16 (G.getD 1 []) (E.getD 1 []) (J.getD 1 []) = true := oddK1
  have h2 : oddOK κCCols liftCCols 11 6 16 (G.getD 2 []) (E.getD 2 []) (J.getD 2 []) = true := oddK2
  have h3 : oddOK κCCols liftCCols 11 6 16 (G.getD 3 []) (E.getD 3 []) (J.getD 3 []) = true := oddK3
  have h4 : oddOK κCCols liftCCols 11 6 32 (G.getD 4 []) (E.getD 4 []) (J.getD 4 []) = true := oddK4
  exact ⟨oddFix_of (by unfold T23s3; congr 1) h0 le_rfl rfl,
    oddFix_of (by unfold T23s5; congr 1) h1 le_rfl rfl,
    oddFix_of (by unfold T23s7; congr 1) h2 le_rfl rfl,
    oddFix_of (by unfold T23s11; congr 1) h3 le_rfl rfl,
    oddFix_of (by unfold T23s23; congr 1) h4 le_rfl rfl⟩

end Certificates
