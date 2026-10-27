module

public import Certificates.Kernel.D4.Facts
public import Certificates.Kernel.D4.LocalUChecks
public import CFSG.Certificates.Kernel.D4WordPosSound

public section

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4Local CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

theorem localU_ok : localUCheck () = true := by
  have hA := evalWA_pos szOK' bindG pGA uWordA (by
    rw [Nat.eq_of_beq_eq_true bG.2.1]
    decide)
  have hB := evalWA_pos szOK' bindGB pGB uWordB (by
    rw [Nat.eq_of_beq_eq_true bGB.2.1]
    decide)
  unfold localUCheck
  rw [lineX0, lineX1, hA.1, hB.1, uFlag_unpack szOK' (pLX 0 (by norm_num)) hA.2,
    uFlag_unpack szOK' (pLX 1 (by norm_num)) hB.2, uA_ok, uB_ok]
  rfl

end CertificateChecks.KernelD4
