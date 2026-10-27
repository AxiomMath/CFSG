module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.GrSLitL34FactsCF23SuzCheck
meta import Certificates.Data.GrSLitL34FactsCF23SuzCheck
import all Certificates.Data.GrSLitL34FactsCF23SuzCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.CF23Suz

open CFSG.ComponentClassification.GSThmB.CF23L34 CFSG.Monster.B.Co2.Native

meta def invsM : Array (Array Nat) :=
  #[invCand 1782 suzY1Arr, invCand 1782 suzY2Arr, invCand 1782 suzMArr]

end CertificateChecks.KernelLC.CF23Suz

#ks_chars CertificateChecks.KernelLC.SuzFus CFSG.ComponentClassification.GSThmB.CF23L34.suzFusText

#kmisc_hexflat CertificateChecks.KernelLC.SuzFus CFSG.ComponentClassification.GSThmB.CF23L34.suzFusText
  3 1782 11 3

#kmisc_packarrs CertificateChecks.KernelLC.SuzFusI CertificateChecks.KernelLC.CF23Suz.invsM 11

namespace CertificateChecks.KernelLC.CF23Suz

open CFSG.KS.Raw CFSG.ComponentClassification.GSThmB.CF23L34 CFSG.Monster.B.Co2.Native

theorem gen_eq {i : Nat} (hi : i < 3) :
    hexTable 3 1782 (1782 * i) suzFusText = unpack 1782 11 (SuzFus.F i) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzFus.all i hi
  rw [← SuzFus.eq] at h
  exact h

theorem y1_eq : suzY1Arr = unpack 1782 11 (SuzFus.F 0) := by
  have h := gen_eq (i := 0) (by norm_num)
  rw [Nat.mul_zero] at h
  unfold suzY1Arr
  exact h

theorem y2_eq : suzY2Arr = unpack 1782 11 (SuzFus.F 1) := by
  have h := gen_eq (i := 1) (by norm_num)
  rw [Nat.mul_one] at h
  unfold suzY2Arr
  exact h

theorem m_eq : suzMArr = unpack 1782 11 (SuzFus.F 2) := by
  have h := gen_eq (i := 2) (by norm_num)
  have e : 1782 * 2 = 3564 := rfl
  rw [e] at h
  unfold suzMArr
  exact h

end CertificateChecks.KernelLC.CF23Suz

end
