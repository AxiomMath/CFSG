
module

public import Certificates.Kernel.Co1M.C10075Base

public import Certificates.Kernel.Co1M.H10075a
public import Certificates.Kernel.Co1M.H10075b
public import Certificates.Kernel.Co1M.T10075
public import CFSG.Certificates.Kernel.Co1M.OrbitSizes

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.Co1B CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.Co1Orb CFSG.KC.PairCount CFSG.Blueprint
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.InvFam
  CFSG.Sporadic.SmallF2 CertificateChecks.KernelVec.Co1

theorem checks_k : orbitCheck 4096 8386560 [1] = true ∧ orbitCheck 1 8292375 [] = true := by
  obtain ⟨x₁, x₂, p₁, p₂, xg, pg⟩ := stab_gens
  obtain ⟨H₃, hH₃, hk₃⟩ := images p₁ p₂ T3_ok u3_lt
  obtain ⟨H₄, hH₄, hk₄⟩ := images p₁ p₂ T4_ok (u := 3) (by norm_num)
  obtain ⟨m1, m2⟩ := and2 mems75
  obtain ⟨-, -, tg⟩ := and3 trs75
  obtain ⟨-, -, fg⟩ := and3 fixes75
  have hw₃ : v₂ + toVecD 24 u3v75 ∈ orb co1Act v₃ := by
    rw [e3, mem_orb]
    refine ⟨xg, ?_⟩
    rw [← toVecD_v₃, pm_act pg (Nat.eq_of_beq_eq_true tg), Nat.eq_of_beq_eq_true fg]
  have hw₄ : v₂ + toVecD 24 3 ∈ orb co1Act v₄ := by
    rw [e4, toVecD_v₄, mem_orb]
    exact ⟨1, co1Act_one _⟩
  have hc₃ : ((orb co1Act v₂).filter fun a => v₂ + toVecD 24 u3v75 + a ∈ orb co1Act v₂).card ≤
      552 := by
    rw [e3]
    exact count_le (J := J3) (by decide +kernel) H3.all
  have hc₄ : ((orb co1Act v₂).filter fun a => v₂ + toVecD 24 3 + a ∈ orb co1Act v₂).card ≤ 552 := by
    rw [e4]
    exact count_le (J := J4) (by norm_num) H4.all
  exact checks_v₃_v₄ orbitCheck_v₂_k ((mem_O2 u3_lt).2 m1) hw₃ H₃ hH₃ hk₃ hc₃
    ((mem_O2 (by norm_num)).2 m2) hw₄ H₄ hH₄ hk₄ hc₄

end CertificateChecks.KernelCo1M

end
