module

public import CFSG.Quasithin.H13.A5M12SylBase
import Certificates.Kernel.HMathieu.Odd
import CFSG.Certificates.Kernel.HMathieu.OddSound

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
open CertificateChecks.KernelHMathieu.Odd

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 in
public theorem certificate7114 :
    
      odd12OK T12s3 mats12s3 ∧ odd12OK T12s5 mats12s5 ∧ odd12OK T12s11 mats12s11 := by
  have h14 : oddOK κC12Cols lift12Cols 10 6 32 (G.getD 14 []) (E.getD 14 []) (J.getD 14 []) =
    true := oddK14
  have h15 : oddOK κC12Cols lift12Cols 10 6 16 (G.getD 15 []) (E.getD 15 []) (J.getD 15 []) =
    true := oddK15
  have h16 : oddOK κC12Cols lift12Cols 10 6 16 (G.getD 16 []) (E.getD 16 []) (J.getD 16 []) =
    true := oddK16
  exact ⟨oddFix_of (by unfold T12s3; congr 1) h14 le_rfl rfl,
    oddFix_of (by unfold T12s5; congr 1) h15 le_rfl rfl,
    oddFix_of (by unfold T12s11; congr 1) h16 le_rfl rfl⟩

end Certificates
