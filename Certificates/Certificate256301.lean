module

public import Certificates.Data.Inputs256cGen5
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Certificates.Data.Inputs256cGen5

public section

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

namespace Certificates

set_option maxHeartbeats 0 in
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c in
theorem certificate256301 : m23Gen5Check = true := by decide +kernel

end Certificates
