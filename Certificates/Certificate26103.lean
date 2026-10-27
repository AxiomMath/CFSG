module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
import Certificates.Kernel.Sporadic.OddCore.SqrtGlue26102
import Certificates.Kernel.SporSch.J3K426.Sift

set_option maxRecDepth 400000

namespace CertificateChecks.Batch26103

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.MulH CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b.TC3H CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.SqrtK26102

theorem cent_eq {k : Nat} (hk : k < 31) : j3CentTbl k = tabT (unpack 6156 13 (J3CentP k)) := by
  rw [← OddCore.j3CentTbl_eq hk, tabT_natArr]

theorem j3 : j3SqrtOK = true := by
  unfold j3SqrtOK
  rw [j3OuterTbl, cent_eq (by norm_num), cent_eq (by norm_num), j3Tbl_eq (by norm_num)]
  refine sqrt_of k26103 fun h => ?_
  obtain ⟨hu, hy⟩ := sqK_canon k26103
  unfold j3Sift
  rw [natArr_tabT (canonK_pcomp hy hu), CertificateChecks.KernelSporSch.J3KT.sift_of h,
    Bool.or_true]

end CertificateChecks.Batch26103

public section

namespace Certificates

open CertificateChecks

theorem certificate26103 : CFSG.EvenSporadicStandard.Fin76b.TC3H.j3SqrtOK = true :=
  CertificateChecks.Batch26103.j3

end Certificates
