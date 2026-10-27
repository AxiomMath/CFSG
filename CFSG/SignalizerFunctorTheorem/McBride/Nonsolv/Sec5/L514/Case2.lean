module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514Aux

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ]

section Finite

variable [Finite Γ]

theorem commutator_smear_projX_le {A G J X : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ)) :
    ⁅smear J A, projX G A J X⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro c hc y hy
  obtain ⟨-, m, hm, hym⟩ := (mem_proj_iff
    (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).commute).mp hy
  have hcL : c ∈ orbitClosure J A := smear_le_orbitClosure J A hc
  have hmc : m * c⁻¹ = c⁻¹ * m :=
    (commute_of_mem_orbitClosure hAG hsol hJ hcL hm).inv_left.eq.symm
  have hcomm : ⁅c, y⁆ = ⁅c, y * m⁆ := by
    calc ⁅c, y⁆ = c * y * (c⁻¹ * m) * m⁻¹ * y⁻¹ := by group
      _ = c * y * (m * c⁻¹) * m⁻¹ * y⁻¹ := by rw [hmc]
      _ = ⁅c, y * m⁆ := by group
  rw [hcomm]
  have hcX := mem_normalizer_of_mem_smear hAG hsol hJ hDX hc
  have hyX : y * m ∈ X := (Subgroup.mem_inf.mp hym).1
  have := (Subgroup.mem_normalizer_iff.mp hcX (y * m)).mp hyX
  exact mul_mem this (inv_mem hyX)

theorem fitting_smear_le_of_projX_inf_ne_bot
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) (hne : projX G A J X ⊓ smear J A ≠ ⊥) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ X := by
  have hAG := h.normalizes
  have hNn : ((projX G A J X ⊓ smear J A).subgroupOf (smear J A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro n c hn hc
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hc (Subgroup.mem_inf.mp hn).2) (inv_mem hc)⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_projX_of_mem_smear hAG hsol hJ.1 hDX hc) n).mp (Subgroup.mem_inf.mp hn).1
  have hFN := fitting_smear_le_of_normal h hJ inf_le_right hNn hne
  obtain ⟨hFs, hFnc⟩ := smear_fitting_isSimple h hJ
  have hperf := commutator_self_eq_of_isSimpleGroup hFnc
  calc CFSG.inSubgroup CFSG.generalizedFitting (smear J A)
      = ⁅CFSG.inSubgroup CFSG.generalizedFitting (smear J A),
          CFSG.inSubgroup CFSG.generalizedFitting (smear J A)⁆ := hperf.symm
    _ ≤ ⁅smear J A, projX G A J X⁆ :=
        Subgroup.commutator_mono (Subgroup.map_subtype_le _) (hFN.trans inf_le_left)
    _ ≤ X := commutator_smear_projX_le hAG hsol hJ.1 hDX

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
