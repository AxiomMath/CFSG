module

public import CFSG.LargeExtraspecial.S63CU33Inputs
import CFSG.Certificates.Kernel.PermCent.U33Sound
import Certificates.Kernel.PermCent.K21110

public section

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.U33T
  CFSG.Certificates.Kernel.PkEnum

namespace Certificates

open CFSG.LargeExtraspecial.S63 in
theorem certificate21110 : u33CentCheck = true := by
  rw [centCheck_eq]
  have hb : ∀ j < 8, centBlk j = true := by
    intro j hj
    interval_cases j
    exacts [centBlk0, centBlk1, centBlk2, centBlk3, centBlk4, centBlk5, centBlk6, centBlk7]
  exact all_of_chunks _ _ 756 8 len21110 hb

end Certificates
