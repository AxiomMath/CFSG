module

public import Certificates.Data.TitsAschbacherNThree
public import Certificates.Kernel.EvenBN.Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27584

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherNThree

set_option simprocs false in
theorem tits_n_three_check_0 : s3Check () = true := by
  have c3 := cV (i := 3) (by norm_num)
  obtain ⟨hw, cw⟩ := w2_eq
  unfold s3Check v3w2Arr
  rw [vA_eq (by norm_num : 3 < 13), hw, CertificateChecks.KernelSporSch.TitsCentral.id_eq]
  simp (config := { maxDischargeDepth := 12 }) only [cmpU, cmpC, eqU, powU, powC, c3, cw, canId]
  quickRfl

end CertificateChecks.Batch27584

namespace Certificates

open CertificateChecks

theorem certificate27584 : Certificates.TitsAschbacherNThree.s3Check () = true := by
  exact CertificateChecks.Batch27584.tits_n_three_check_0

end Certificates
