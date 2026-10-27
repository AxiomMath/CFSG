module

public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G]

theorem commutator_sup_le_of_conj {Y N C A B : Subgroup G} (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hN : ∀ g ∈ Y, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hA : ⁅C, A⁆ ≤ N) (hB : ⁅C, B⁆ ≤ N) :
    ⁅C, A ⊔ B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro c hc g hg
  have key : g ∈ Y ∧ ⁅c, g⁆ ∈ N := by
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨hAY hx, hA (Subgroup.commutator_mem_commutator hc hx)⟩
      · exact ⟨hBY hx, hB (Subgroup.commutator_mem_commutator hc hx)⟩
    | one => exact ⟨Y.one_mem, by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨Y.mul_mem iha.1 ihb.1, ?_⟩
      have e : ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem iha.2 (hN a iha.1 _ ihb.2)
    | inv a _ iha =>
      refine ⟨Y.inv_mem iha.1, ?_⟩
      have e : ⁅c, a⁻¹⁆ = a⁻¹ * ⁅c, a⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hN a⁻¹ (Y.inv_mem iha.1) _ (N.inv_mem iha.2)
  exact key.2

section Fin

variable [Finite G]

theorem eq_or_eq_of_mem_cComp_of_le_sup {Y K₁ K₂ C : Subgroup G} (h₁ : K₁ ∈ cComp Y)
    (h₂ : K₂ ∈ cComp Y) (hC : C ∈ cComp Y) (hCK : C ≤ K₁ ⊔ K₂) : C = K₁ ∨ C = K₂ := by
  by_contra hne
  obtain ⟨hne₁, hne₂⟩ := not_or.mp hne
  have hsp : K₁ ⊔ K₂ ≤ cCompSpan Y := sup_le (le_cCompSpan h₁) (le_cCompSpan h₂)
  have hnorm : ∀ {K : Subgroup G}, K ∈ cComp Y → cCompSpan Y ≤ Subgroup.normalizer (K : Set G) :=
    fun hK => (Subgroup.normal_subgroupOf_iff_le_normalizer (le_cCompSpan hK)).mp
      (cComp_normal_span_of_le hK).2
  have key : ∀ {K : Subgroup G}, K ∈ cComp Y → C ≠ K → ⁅C, K⁆ ≤ solvRad Y := by
    intro K hK hCK'
    rcases cComp_commutator_dichotomy_of_le hC (le_of_mem_cComp hK) with ⟨h, -⟩ | h
    · exact h
    · exfalso
      have hCN : C ≤ Subgroup.normalizer (K : Set G) := hCK.trans (hsp.trans (hnorm hK))
      have hCK1 : C ≤ K :=
        calc C ≤ conjClosure C K := le_conjClosure C K
          _ = ⁅C, K⁆ := h.symm
          _ ≤ K := Subgroup.le_normalizer_iff_commutator_le_right.mp hCN
      exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hCK1 hCK') (ne_bot_of_mem_cComp hC)
        (perfect_of_mem_cComp hC) (subnormal_of_mem_cComp hC)
  have hcomm : ⁅C, K₁ ⊔ K₂⁆ ≤ solvRad Y :=
    commutator_sup_le_of_conj (le_of_mem_cComp h₁) (le_of_mem_cComp h₂)
      (fun _ hg _ hx => conj_mem_solvRad (Subgroup.le_normalizer hg) hx)
      (key h₁ hne₁) (key h₂ hne₂)
  have hCs : C ≤ solvRad Y :=
    calc C = ⁅C, C⁆ := (perfect_of_mem_cComp hC).symm
      _ ≤ ⁅C, K₁ ⊔ K₂⁆ := Subgroup.commutator_mono le_rfl hCK
      _ ≤ solvRad Y := hcomm
  have := solvRad_isSolvable Y
  exact not_isSolvable_of_mem_cComp hC (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hCs) (Subgroup.inclusion_injective hCs))

end Fin

end SBc13

end CFSG.Quasithin
