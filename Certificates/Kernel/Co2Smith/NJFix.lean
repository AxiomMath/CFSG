module

public import Certificates.Kernel.Co2Smith.W
public import Certificates.Kernel.Co2Smith.Pts
public import Certificates.Kernel.Co2Smith.NJFixK0
public import Certificates.Kernel.Co2Smith.NJFixK1
public import Certificates.Kernel.Co2Smith.NJFixK2
public import Certificates.Kernel.Co2Smith.NJFixK3
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Smith.GlNJInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch.Co2M

theorem njFixR_eq (A : Nat) : glNJFixR (unpackR 22 A) = fixVK A := by
  unfold glNJFixR fixVK
  simp only
  rw [tr_sound (Nat.beq_refl _)]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [V_get (List.mem_range.1 hi), colActT, CFSG.KC.F2W.vecMulN_unpackR]
  by_cases e : CFSG.KC.M1F2.vmF 22 (trK 22 A) (CFSG.KS.Co2M.VG (PV 0) i) = CFSG.KS.Co2M.VG (PV 0) i
  · rw [e, Nat.beq_refl]
    exact beq_self_eq_true _
  · rw [beq_eq_false_iff_ne.2 e, beq_false e]

theorem njFix_chunk {lo m : Nat} (h : njFixK lo 256 = true) (h1 : lo ≤ m) (h2 : m < lo + 256) :
    (m == 0 || glNJOm.contains m || glNJFixR (glJcR m) != 284) = true := by
  unfold njFixK at h
  have hj := List.all_eq_true.1 h (m - lo) (List.mem_range.2 (by omega))
  rw [Nat.add_sub_cancel' h1] at hj
  rw [jc_eq, njFixR_eq]
  exact hj

theorem njFix_ok : glNJFixOK = true := by
  unfold glNJFixOK
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  by_cases a : m < 256
  · exact njFix_chunk njFix_k0 (by omega) (by omega)
  by_cases b : m < 512
  · exact njFix_chunk njFix_k1 (by omega) (by omega)
  by_cases c : m < 768
  · exact njFix_chunk njFix_k2 (by omega) (by omega)
  · exact njFix_chunk njFix_k3 (by omega) (by omega)

end CertificateChecks.KernelCo2Smith
