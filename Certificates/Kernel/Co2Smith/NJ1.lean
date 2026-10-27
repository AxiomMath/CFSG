module

public import Certificates.Kernel.Co2Smith.W
public import Certificates.Kernel.Co2Smith.NJ1K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem njGw_k : (glNJGw.size == 3 && (List.range 3).all fun k => glNJGw[k]!.all (· < 22)) = true := by
  decide +kernel

theorem njG_eq {k : Nat} (hk : k < 3) : glNJG k = unpackR 22 (njGK k) := by
  have h := njGw_k
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact glR_eq (h.2 k hk)

theorem njGen_ok : glNJGenOK = true := by
  rw [← njGen_k]
  unfold glNJGenOK njGenK
  rw [← Array.all_toList, njG_eq (by decide), njG_eq (by decide), glZ_eq, commRows_unpack,
    commRows_unpack]
  congr 1
  apply all_congr_mem
  intro k hk
  rw [List.mem_range] at hk
  rw [glNJGt, njG_eq hk, jc_eq, mulRows_unpack, tab_eq, tab_eq]

theorem njInj_ok : glNJInjOK = true := by
  rw [← njInj_k]
  unfold glNJInjOK njInjK
  simp only [jc_eq, idRows_eq, bne_unpack]

theorem nj1_ok : glNJ1OK = true := by
  unfold glNJ1OK
  rw [njGen_ok, njInj_ok, njOm_k]
  rfl

end CertificateChecks.KernelCo2Smith
