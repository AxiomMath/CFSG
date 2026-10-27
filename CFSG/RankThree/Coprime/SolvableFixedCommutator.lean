module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.Coprime

open CFSG.LocalAnalysis.ComponentInitial

variable {A H : Type*} [Group A] [Group H] [MulDistribMulAction A H]

theorem isInvariant_actionCommutator_top :
    CFSG.IsInvariant A H (actionCommutator A (⊤ : Subgroup H)) :=
  ⟨fun a g => ⟨fun hg => smul_mem_actionCommutator_top hg a, fun hg => by
    have := smul_mem_actionCommutator_top hg a⁻¹
    rwa [inv_smul_smul] at this⟩⟩

theorem solvable_coprime_fixed_commutator_factorization [Finite A] [Finite H]
    (hH : Group.IsSolvable H) (hcop : Nat.Coprime (Nat.card H) (Nat.card A)) :
    (actionCommutator A (⊤ : Subgroup H)).Normal ∧
    (∀ a : A, ∀ x ∈ actionCommutator A (⊤ : Subgroup H),
      a • x ∈ actionCommutator A (⊤ : Subgroup H)) ∧
    (∀ h : H, ∃ d ∈ actionCommutator A (⊤ : Subgroup H),
      ∃ c ∈ CFSG.fixedPointSubgroup A H, h = d * c) ∧
    actionCommutator A (actionCommutator A (⊤ : Subgroup H)) =
      actionCommutator A (⊤ : Subgroup H) := by
  classical
  set D := actionCommutator A (⊤ : Subgroup H) with hD
  have hDn : D.Normal := actionCommutator_top_normal
  have hDinv : CFSG.IsInvariant A H D := isInvariant_actionCommutator_top
  have hcopD : Nat.Coprime (Nat.card A) (Nat.card D) :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card D) hcop).symm
  have hDsolv : Group.IsSolvable D := by
    have := hH
    infer_instance
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting D hDinv hDsolv hcopD
  have hfac : ∀ q : H, ∃ d ∈ D, ∃ c ∈ CFSG.fixedPointSubgroup A H, q = d * c := by
    intro q
    let : MulDistribMulAction A (H ⧸ D) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := H) D hDinv
    let : MulAction.QuotientAction A D := CFSG.quotientAction_of_isInvariant (A := A) D hDinv
    have hq : (q : H ⧸ D) ∈ CFSG.fixedPointSubgroup A (H ⧸ D) := by
      intro a
      rw [MulAction.Quotient.smul_coe (H := D) a q, QuotientGroup.eq]
      have h := gen_mem_actionCommutator (A := A) (Subgroup.mem_top q) a⁻¹
      have h' : (a • q)⁻¹ * q = a • (q⁻¹ * (a⁻¹ • q)) := by
        rw [smul_mul', smul_inv', smul_inv_smul]
      rw [h']
      exact smul_mem_actionCommutator_top h a
    rw [hlift] at hq
    obtain ⟨c, hc, hcq⟩ := hq
    have hcq' : c⁻¹ * q ∈ D := QuotientGroup.eq.1 hcq
    refine ⟨q * c⁻¹, ?_, c, hc, by rw [inv_mul_cancel_right]⟩
    have := hDn.conj_mem _ hcq' c
    rwa [mul_inv_cancel_left] at this
  refine ⟨hDn, fun a x hx => smul_mem_actionCommutator_top hx a, hfac, le_antisymm ?_ ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, -, a, rfl⟩
    exact gen_mem_actionCommutator (Subgroup.mem_top d) a
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q, -, a, rfl⟩
    obtain ⟨d, hd, c, hc, rfl⟩ := hfac q
    have hac : a • c = c := hc a
    have hdc : c⁻¹ * d * c ∈ D := by simpa using hDn.conj_mem d hd c⁻¹
    have h : (d * c)⁻¹ * (a • (d * c)) = (c⁻¹ * d * c)⁻¹ * (a • (c⁻¹ * d * c)) := by
      simp only [smul_mul', smul_inv', hac]
      group
    rw [h]
    exact gen_mem_actionCommutator hdc a

end CFSG.RankThree.Coprime
