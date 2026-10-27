module

public import Certificates.Data.Co2Cent
public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public meta import Certificates.Data.Co2Cent
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelCo2I301.CH CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2Hex
#kmisc_hexflat CertificateChecks.KernelCo2I301.CH CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2Hex
  3 2300 12 43

namespace CertificateChecks.KernelCo2I301

open CFSG.HardMathSupport.Dickson.I271.Co2Cent

theorem co2Arr_eq (k : ℕ) (hk : k < 43) : co2Arr k = CFSG.KS.Raw.unpack 2300 12 (CH.F k) := by
  unfold co2Arr
  rw [CH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CH.all k hk

@[expose] def lD : List (List ℤ) := co2LWords.toList.drop 2

meta def lS : Array (Array ℕ) := co2LArrs ()

end CertificateChecks.KernelCo2I301

end

#ks_rawchain_sl2_data CertificateChecks.KernelCo2I301.LC 2300 12 0 2300
  CertificateChecks.KernelCo2I301.lS CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LBase 2
  CertificateChecks.KernelCo2I301.lD
#ks_rawchain_sl2_lvp CertificateChecks.KernelCo2I301.LC 0 0 1
#ks_rawchain_sl2_lvp CertificateChecks.KernelCo2I301.LC 1 0 1
#ks_rawchain_sl2_lvp CertificateChecks.KernelCo2I301.LC 2 0 1
#ks_rawchain_sl2_join CertificateChecks.KernelCo2I301.LC

public section

namespace CertificateChecks.KernelCo2I301.LC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem bS : allN 6 (fun j => Nat.beq (S j) (CertificateChecks.KernelCo2I301.CH.F (37 + j))) =
    true := by
  quickRfl

theorem perm : allN 6 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 3, CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LBase[t]! =
    pg 12 (mask 12) BP t := by
  decide +kernel

end CertificateChecks.KernelCo2I301.LC

end
