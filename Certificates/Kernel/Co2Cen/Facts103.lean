module

public import Certificates.Kernel.Co2Cen.GlueBase
public import Certificates.Kernel.Co2Cen.Scan4
public import CFSG.RankThree.Co2.ZP4Facts

public section

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.Co2Cen
  CFSG.KC.TabMatGrp CertificateChecks.KernelSpor.Co2Syl CertificateChecks.KernelSpor.Co2Cls
  CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem scan_none {CF : ℕ → ℕ} {T k : ℕ}
    (h : scanC CF (fun _ => 0) (fun _ _ => false) T 0 k = true) :
    MatP 22 (elemAt CF k) * MatP 22 T ≠ MatP 22 T * MatP 22 (elemAt CF k) := by
  intro hc
  unfold scanC at h
  simp only [letB_eq] at h
  have hb : Nat.beq (mulV (elemAt CF k) T) (mulV T (elemAt CF k)) = true := by
    rw [← MatP_mulV, ← MatP_mulV] at hc
    rw [MatP_inj' (mulV_lt _ _) (mulV_lt _ _) hc, Nat.beq_refl]
  rw [implK_eq, hb, if_pos rfl, bIf_eq'] at h
  have hf : scFlag 0 = false := by decide
  rw [hf, if_neg Bool.false_ne_true] at h
  unfold scRank at h
  have hr : scRk 0 = 0 := by decide
  simp only [letB_eq, hr, andK_eq, notK_eq, Nat.beq_refl, Bool.not_true, Bool.false_and,
    Bool.and_false] at h
  exact Bool.false_ne_true h

theorem G4_mem : MatP 22 (G4 0) ∈ matGrp pWords4 := by
  rw [← genMon4]
  exact gen_mem G4 (by norm_num)

theorem zp4_facts {x : M22} (_hx : x ∈ matGrp pWords4)
    (hz : ∀ y ∈ matGrp pWords4, x * y = y * x) :
    ¬ CrConj (repMat 2) x ∧ ¬ CrConj (repMat 7) x := by
  have hc := hz _ G4_mem
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := rec_of_conj2 h
    exact scan_none (scan24 k hk) hc
  · obtain ⟨k, hk, rfl⟩ := rec_of_conj7 h
    exact scan_none (scan74 k hk) hc

theorem zp4Facts : ZP4Facts := fun _ _ hx hz => zp4_facts hx hz

end CertificateChecks.KernelSpor.Co2Cen

end
