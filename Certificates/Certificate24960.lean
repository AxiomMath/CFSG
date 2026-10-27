module

import Certificates.Kernel.Sporadic.Co2.HypGlue
import Certificates.Kernel.Sporadic.Co2.Sq
public import CFSG.Assembly.Defs
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase

namespace CertificateChecks.KernelSpor.Co2SQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Cert
open CFSG.KS.Raw.Orb (PRep)
open CertificateChecks.KernelCo2Smith (permK prep_of_permOK mem_P_of_sift prep_unique)

theorem sq_of {W I R : Nat}
    {r : Equiv.Perm (Fin 2300)} (hR : PRep 2300 12 R r) (h : sqK W I R = true) :
    ∃ w ∈ co2P, w * w = r := by
  unfold sqK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hs⟩, hq⟩ := h
  have hW := prep_of_permOK hp
  have h2 := Co2HG.prep_c hW hW
  rw [Nat.eq_of_beq_eq_true hq] at h2
  exact ⟨permK W, mem_P_of_sift hW hs, prep_unique h2 hR⟩

end CertificateChecks.KernelSpor.Co2SQ

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier in
theorem certificate24960 : (∃ w ∈ co2P, w * w = locZ) ∧ (∃ w ∈ co2P, w * w = locT) ∧ (∃ w ∈ co2P, w * w = locU) :=
  ⟨KernelSpor.Co2SQ.sq_of KernelSpor.Co2HG.prep_z KernelSpor.Co2SQ.sqZ,
    KernelSpor.Co2SQ.sq_of KernelSpor.Co2HG.prep_t KernelSpor.Co2SQ.sqT,
    KernelSpor.Co2SQ.sq_of KernelSpor.Co2HG.prep_u KernelSpor.Co2SQ.sqU⟩

end Certificates
