module

public import Certificates.Kernel.Co1M.C16954
public import Certificates.Kernel.Co1M.O10075
public import Certificates.Kernel.Co1B.Iota
public import CFSG.Certificates.Kernel.Co1M.C16954Glue

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2 CFSG.KC.Co1M
  CFSG.KC.VecK CertificateChecks.KernelVec.Co1

theorem mem_certX_iff
    {w : Nat} (hw : w < 2 ^ 24) :
    orbMemK 98280 (lk S 32) 17 w = true ↔ toVecD 24 w ∈ certX := by
  rw [certX_eq_co1X, ← cm_orb_inPts, ← orb2_eq, inPts2_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [← e]; rfl⟩
  · rintro ⟨i, hi, e⟩
    refine ⟨i, hi, toVecD_injective ?_ hw e.symm⟩
    rw [pts2 hi]
    exact Pt_lt hi

theorem rep_R0 :
    MRep (CFSG.KC.Co1F2.unpackR 24 CertificateChecks.KernelCo1Cover.R0) A₁ := by
  rw [← CertificateChecks.KernelCo1B.aR_eq]
  exact rep_A₁

theorem rep_R1 :
    MRep (CFSG.KC.Co1F2.unpackR 24 CertificateChecks.KernelCo1Cover.R1) A₂ := by
  rw [← CertificateChecks.KernelCo1B.bR_eq]
  exact rep_A₂

theorem co1_eleven_k
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≤ 66 ∧
      3 ∣ Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) :=
  CFSG.KC.Co1ElevenGlue.co1_eleven_of_check c16954_ok rep_R0 rep_R1
    (fun _ hw => mem_certX_iff hw) x hx

end CertificateChecks.KernelCo1M

end
