module

public import Certificates.Data.CFSGNative.Fi23.Data
import CFSG.Certificates.Kernel.Spor.F3LaneEq
import CFSG.Certificates.Kernel.Spor.F3LaneRowsSound
import Certificates.Kernel.SporDet.Fi23

public section

set_option maxRecDepth 400000

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi23

namespace CertificateChecks.Batch9000

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23
open CFSG.F3.Native CFSG.KS.F3L CertificateChecks.KernelDet.Fi23

private theorem idM_eq : idM 253 = unlane 253 LI := idM_of_idOK id_ok

private theorem rowsA : rowsOf 253 Native.seedA = unlane 253 LA := by
  rw [SeedA.eq]
  exact rowsOf_seedRows (by norm_num) seedA_ok

private theorem rowsB : rowsOf 253 Native.seedB = unlane 253 LB := by
  rw [SeedB.eq]
  exact rowsOf_seedRows (by norm_num) seedB_ok

private theorem rows_B_cube :
    eqM 253 (powM 253 (rowsOf 253 Native.seedB) 3) (idM 253) = true := by
  have hd : 0 < 253 := by norm_num
  simp only [rowsB, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq b3_ok

private theorem rows_E_pow :
    eqM 253 (powM 253 (mul 253
      (powM 253 (mul 253 (rowsOf 253 Native.seedA) (rowsOf 253 Native.seedB)) 5)
      (powM 253 (mul 253 (rowsOf 253 Native.seedA)
        (mul 253 (rowsOf 253 Native.seedB) (rowsOf 253 Native.seedB))) 2)) 5) (idM 253) = true := by
  have hd : 0 < 253 := by norm_num
  simp only [rowsA, rowsB, mul_unlane hd, powM_unlane hd idM_eq]
  rw [idM_eq]
  exact eqM_of_beq e5_ok

end CertificateChecks.Batch9000

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 in
open CFSG.F3.Native in
theorem certificate9000 : (eqM 253 (powM 253 (CFSG.F3.Native.rowsOf 253 Native.seedB) 3) (CFSG.F3.Native.idM 253) = true)
    ∧ (eqM 253 (powM 253 (CFSG.F3.Native.mul 253
      (powM 253 (CFSG.F3.Native.mul 253 (CFSG.F3.Native.rowsOf 253 Native.seedA) (CFSG.F3.Native.rowsOf 253 Native.seedB)) 5)
      (powM 253 (CFSG.F3.Native.mul 253 (CFSG.F3.Native.rowsOf 253 Native.seedA)
        (CFSG.F3.Native.mul 253 (CFSG.F3.Native.rowsOf 253 Native.seedB) (CFSG.F3.Native.rowsOf 253 Native.seedB))) 2)) 5) (CFSG.F3.Native.idM 253) = true) :=
  ⟨CertificateChecks.Batch9000.rows_B_cube, CertificateChecks.Batch9000.rows_E_pow⟩

end Certificates

end
