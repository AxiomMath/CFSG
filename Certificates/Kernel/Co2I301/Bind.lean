module

public import CFSG.Sporadic.Co2I301.Inputs
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public meta import CFSG.Sporadic.Co2I301.Inputs
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo2I301.HX CFSG.Sporadic.Co2I301.i301Hex
#kmisc_hexflat CertificateChecks.KernelCo2I301.HX CFSG.Sporadic.Co2I301.i301Hex 3 2300 12 10

namespace CertificateChecks.KernelCo2I301

open CFSG.Sporadic.Co2I301

theorem arr_eq (k : ℕ) (hk : k < 10) : i301Arr k = CFSG.KS.Raw.unpack 2300 12 (HX.F k) := by
  unfold i301Arr
  rw [HX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound HX.all k hk

end CertificateChecks.KernelCo2I301

end
