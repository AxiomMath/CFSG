module

public import CFSG.Milestones.ASVolI.F431.BCoreGen

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin

section Perfect

theorem burnsideF4m_perfect_map {A B : Type} [Group A] [Group B] (φ : A →* B) {S : Subgroup A}
    (hS : ⁅S, S⁆ = S) : ⁅S.map φ, S.map φ⁆ = S.map φ := by
  rw [← Subgroup.map_commutator, hS]

theorem burnsideF4m_perf_transport {C D : Type} [Group C] [Group D] (e : C ≃* D)
    (h : ∀ S : Subgroup (MulAut C), ⁅S, S⁆ = S → S ≤ (MulAut.conj : C →* MulAut C).range)
    (S : Subgroup (MulAut D)) (hS : ⁅S, S⁆ = S) :
    S ≤ (MulAut.conj : D →* MulAut D).range := by
  intro α hα
  have h1 := h (S.map (MulAut.congr e).symm.toMonoidHom)
    (burnsideF4m_perfect_map _ hS) ⟨α, hα, rfl⟩
  obtain ⟨g, hg⟩ := h1
  refine ⟨e g, ?_⟩
  have h2 := congrArg (MulAut.congr e) hg
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
  rw [← h2]
  exact (burnsideF4m_congr_conj e g).symm

theorem burnsideF4m_perfectCore_eq_inf_of_perfect {E : Type} [Group E] [Finite E]
    {Gp : Subgroup E} [Gp.Normal] (hcen : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hperf : ∀ S : Subgroup (MulAut ↥Gp), ⁅S, S⁆ = S →
      S ≤ (MulAut.conj : ↥Gp →* MulAut ↥Gp).range) (M : Subgroup E) :
    perfectCore M = perfectCore (Gp ⊓ M) := by
  have hinj := burnsideF4d_rho_injective hcen
  have hP := perfectCore_perfect M
  have h1 := hperf _ (burnsideF4m_perfect_map (burnsideF4d_rho Gp) hP)
  have hle : perfectCore M ≤ Gp := by
    intro x hx
    obtain ⟨g, hg⟩ := h1 ⟨x, hx, rfl⟩
    have hgx : burnsideF4d_rho Gp (g : E) = burnsideF4d_rho Gp x := by
      rw [← hg]
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [burnsideF4d_rho_apply]
      rfl
    rw [← hinj hgx]
    exact g.2
  refine le_antisymm ?_ (perfectCore_mono inf_le_right)
  exact le_perfectCore_of_perfect (le_inf hle (perfectCore_le M)) hP

variable {E C : Type} [Group E] [Group C] {Gp M : Subgroup E}

theorem burnsideF4m_core1_of_model' (hpc : perfectCore M = perfectCore (Gp ⊓ M)) (φ : C →* E)
    (hφ : Function.Injective φ) {P : Subgroup C} (hP : Gp ⊓ M = P.map φ)
    (hm : centerOf (perfectCore P) ≤ ctr (oPPrime 2 P)) :
    ∀ x ∈ centerOf (perfectCore M), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M)) := by
  intro x hx _ _
  rw [hpc, hP, burnsideF4m_perfectCore_map φ hφ, burnsideF4m_centerOf_map φ hφ] at hx
  rw [hP, burnsideF4gD4Inv_map_oPPrime φ hφ, burnsideF4m_ctr_map φ hφ]
  exact Subgroup.map_mono hm hx

theorem burnsideF4m_centerOf_perfectCore_eq_bot_of_model'
    (hpc : perfectCore M = perfectCore (Gp ⊓ M)) (φ : C →* E) (hφ : Function.Injective φ)
    {P : Subgroup C} (hP : Gp ⊓ M = P.map φ) (hm : centerOf (perfectCore P) = ⊥) :
    centerOf (perfectCore M) = ⊥ := by
  rw [hpc, hP, burnsideF4m_perfectCore_map φ hφ, burnsideF4m_centerOf_map φ hφ, hm,
    Subgroup.map_bot]

end Perfect

end CFSG.ASVolI
