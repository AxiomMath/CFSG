module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
import Certificates.Kernel.Sporadic.OddCore.SqrtGlue26102
import Certificates.Kernel.Sporadic.OddCore.J2CnF

set_option maxRecDepth 400000

namespace CertificateChecks.Batch26102

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.MulH CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.Fin76b.TC3H CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.SqrtK26102

theorem sift_of {y : Nat} {a : Nat} {s : Bool}
    (h : sqK 315 9 (J2Cn.F 0) a y s = true)
    (hs : s = (J2Cn.sK y || J2Cn.sK (pcomp 315 9 (mask 9) y (J2Cn.F 0)))) :
    s = true → (j2Sift (tabT (unpack 315 9 y)) ||
      j2Sift (tabT (unpack 315 9 (pcomp 315 9 (mask 9) y (J2Cn.F 0))))) = true := by
  obtain ⟨hu, hy⟩ := sqK_canon h
  rw [J2Cn.sift_eq hy, J2Cn.sift_eq (canonK_pcomp hy hu), ← hs]
  exact id

theorem j2 : j2SqrtOK = true := by
  unfold j2SqrtOK
  rw [j2OuterTbl, J2Cn.tabF (by norm_num : 0 < 42), J2Cn.tabF (by norm_num : 31 < 42),
    J2Cn.tabF (by norm_num : 17 < 42), j2Tbl_eq (by norm_num), j2Tbl_eq (by norm_num),
    sqrt_of k26102_a (sift_of k26102_a rfl), sqrt_of k26102_b (sift_of k26102_b rfl)]
  rfl

end CertificateChecks.Batch26102

public section

namespace Certificates

open CertificateChecks

theorem certificate26102 : CFSG.EvenSporadicStandard.Fin76b.TC3H.j2SqrtOK = true :=
  CertificateChecks.Batch26102.j2

end Certificates
