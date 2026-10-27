module

public import Certificates.Data.W115Rank34
import Certificates.Kernel.F2Rank34.Checks
import CFSG.Certificates.Kernel.F2Rank34.Sound

public section

open CFSG.KC.F2R34

namespace Certificates

open CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22 in
theorem certificate1037115 :
    mulT (mulT w115PA (subIdT (tab34P w115HA))) w115QA = idT 24 ∧
    mulT (mulT w115PD (subIdT (tab34P w115HD))) w115QD = idT 24 ∧
    mulT (mulT w115PR (subIdT (tab34P w115HR))) w115QR = idT 24 :=
  ⟨check34_sound _ _ _ _ _ rankA, check34_sound _ _ _ _ _ rankD,
    check34_sound _ _ _ _ _ rankR⟩

end Certificates
