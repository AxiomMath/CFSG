module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.SquareCheck
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Kernel.Sporadic.Co3.Single
import Certificates.Kernel.Co3Square.Check
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.Co3Sylow

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Square

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CertificateChecks.KernelSpor
  CFSG.Sporadic.Schreier.Co3

theorem tArr0 : co3TArrs[0]! = unpack 276 9 (Co3Text.L (Nat.add 35 0)) :=
  (Co3Text.field_of (f := 5) (F := fun j => Co3Text.L (Nat.add 35 j)) rfl (by norm_num)
    (by quickRfl)).2 0 (by norm_num)

theorem co3SquareCheck_true : CFSG.EvenSporadicStandard.Co3Std.co3SquareCheck = true := by
  rw [CFSG.EvenSporadicStandard.Co3Std.co3SquareCheck.eq_1, tArr0, Co3Single.z_eq,
    compA_unpack canon_t0 canon_t0, eqA_unpack canon_sq canon_z]
  exact sq_t0

end CertificateChecks.KernelCo3Square

end
