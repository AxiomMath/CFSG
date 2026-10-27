module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.Fi24.Data
import CFSG.Certificates.Kernel.Spor.F3LaneEq
import CFSG.Certificates.Kernel.Spor.F3LaneRowsSound
import Certificates.Kernel.SporDet.Fi24

public section

set_option maxRecDepth 400000

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi24

namespace CertificateChecks.Batch9001

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi24

private theorem idM_eq : idM 781 = unlane 781 LI := idM_of_idOK id_ok

private theorem rowsA : rowsOf 781 Native.seedA = unlane 781 LA := by
  rw [CFSG.KD.BrFi24.SA.eq]
  exact rowsOf_seedRows (by norm_num) seedA_ok

private theorem rowsB : rowsOf 781 Native.seedB = unlane 781 LB := by
  rw [CFSG.KD.BrFi24.SB.eq]
  exact rowsOf_seedRows (by norm_num) seedB_ok

private theorem rows_B_cube :
    eqM 781 (powM 781 (rowsOf 781 Native.seedB) 3) (idM 781) = true := by
  have hd : 0 < 781 := by norm_num
  simp only [rowsB, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq b3_ok

private theorem rows_AB_pow :
    eqM 781 (powM 781 (mul 781 (rowsOf 781 Native.seedA) (rowsOf 781 Native.seedB)) 29)
      (idM 781) = true := by
  have hd : 0 < 781 := by norm_num
  simp only [rowsA, rowsB, mul_unlane hd, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq ab29_ok

end CertificateChecks.Batch9001

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi24 in
open CFSG.F3.Native in
theorem certificate9001 : (eqM 781 (powM 781 (CFSG.F3.Native.rowsOf 781 Native.seedB) 3) (CFSG.F3.Native.idM 781) = true)
    ∧ (eqM 781 (powM 781 (CFSG.F3.Native.mul 781 (CFSG.F3.Native.rowsOf 781 Native.seedA) (CFSG.F3.Native.rowsOf 781 Native.seedB)) 29)
      (CFSG.F3.Native.idM 781) = true) :=
  ⟨CertificateChecks.Batch9001.rows_B_cube, CertificateChecks.Batch9001.rows_AB_pow⟩

end Certificates

end
