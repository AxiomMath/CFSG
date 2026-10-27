module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

namespace PinnedAut

variable {L : Type*} [Group L] (P : PinnedAut L)

structure Separated : Prop where
  field_normalizes : ∀ φ ∈ P.field, ∀ d ∈ P.inndiag, φ * d * φ⁻¹ ∈ P.inndiag
  graph_normalizes : ∀ γ ∈ P.graph, ∀ d ∈ P.inndiag, γ * d * γ⁻¹ ∈ P.inndiag
  field_inter : ∀ φ ∈ P.field, φ ∈ P.inndiag → φ = 1
  graph_out : ∀ γ ∈ P.graph, γ ≠ 1 → ∀ d ∈ P.inndiag, ∀ φ ∈ P.field, γ ≠ d * φ
  graph_graphField : ∀ γ ∈ P.graph, ∀ γ' ∈ P.graph, ∀ φ ∈ P.field, φ ≠ 1 →
    ∀ d ∈ P.inndiag, γ ≠ d * (γ' * φ)

theorem Separated.of_graph_eq_empty (hΓ : P.graph = ∅)
    (hnorm : ∀ φ ∈ P.field, ∀ d ∈ P.inndiag, φ * d * φ⁻¹ ∈ P.inndiag)
    (hinter : ∀ φ ∈ P.field, φ ∈ P.inndiag → φ = 1) : P.Separated where
  field_normalizes := hnorm
  graph_normalizes γ hγ := by rw [hΓ] at hγ; exact absurd hγ (Set.notMem_empty γ)
  field_inter := hinter
  graph_out γ hγ := by rw [hΓ] at hγ; exact absurd hγ (Set.notMem_empty γ)
  graph_graphField γ hγ := by rw [hΓ] at hγ; exact absurd hγ (Set.notMem_empty γ)

variable {P}

section Cosets

variable (hP : P.Separated) {τ : MulAut L}
include hP

theorem Separated.exists_mul_inv_mem_of_isField (hτ : P.IsField τ) :
    ∃ φ ∈ P.field, φ ≠ 1 ∧ τ * φ⁻¹ ∈ P.inndiag := by
  obtain ⟨φ, hφ, h1, d, hd, rfl⟩ := hτ
  refine ⟨φ, hφ, h1, ?_⟩
  rw [show d * φ * d⁻¹ * φ⁻¹ = d * (φ * d⁻¹ * φ⁻¹) by group]
  exact mul_mem hd (hP.field_normalizes φ hφ d⁻¹ (inv_mem hd))

theorem Separated.exists_mul_inv_mem_of_isGraph (hτ : P.IsGraph τ) :
    ∃ γ ∈ P.graph, γ ≠ 1 ∧ τ * γ⁻¹ ∈ P.inndiag := by
  obtain ⟨γ, hγ, h1, d, hd, rfl⟩ := hτ
  refine ⟨γ, hγ, h1, ?_⟩
  rw [show d * γ * d⁻¹ * γ⁻¹ = d * (γ * d⁻¹ * γ⁻¹) by group]
  exact mul_mem hd (hP.graph_normalizes γ hγ d⁻¹ (inv_mem hd))

theorem Separated.exists_mul_inv_mem_of_isGraphField (hτ : P.IsGraphField τ) :
    ∃ γ ∈ P.graph, γ ≠ 1 ∧ ∃ φ ∈ P.field, φ ≠ 1 ∧ τ * (γ * φ)⁻¹ ∈ P.inndiag := by
  obtain ⟨γ, hγ, hγ1, φ, hφ, hφ1, d, hd, rfl⟩ := hτ
  refine ⟨γ, hγ, hγ1, φ, hφ, hφ1, ?_⟩
  rw [show d * (γ * φ) * d⁻¹ * (γ * φ)⁻¹ = d * (γ * (φ * d⁻¹ * φ⁻¹) * γ⁻¹) by group]
  exact mul_mem hd (hP.graph_normalizes γ hγ _ (hP.field_normalizes φ hφ d⁻¹ (inv_mem hd)))

theorem Separated.not_mem_inndiag_of_isField (hτ : P.IsField τ) : τ ∉ P.inndiag := by
  intro hmem
  obtain ⟨φ, hφ, h1, hc⟩ := hP.exists_mul_inv_mem_of_isField hτ
  refine h1 (hP.field_inter φ hφ ?_)
  rw [show φ = (τ * φ⁻¹)⁻¹ * τ by group]
  exact mul_mem (inv_mem hc) hmem

theorem Separated.not_mem_inndiag_of_isGraph (hτ : P.IsGraph τ) : τ ∉ P.inndiag := by
  intro hmem
  obtain ⟨γ, hγ, h1, hc⟩ := hP.exists_mul_inv_mem_of_isGraph hτ
  exact hP.graph_out γ hγ h1 ((τ * γ⁻¹)⁻¹ * τ) (mul_mem (inv_mem hc) hmem) 1 (one_mem _)
    (by group)

theorem Separated.not_mem_inndiag_of_isGraphField (hτ : P.IsGraphField τ) : τ ∉ P.inndiag := by
  intro hmem
  obtain ⟨γ, hγ, hγ1, φ, hφ, -, hc⟩ := hP.exists_mul_inv_mem_of_isGraphField hτ
  exact hP.graph_out γ hγ hγ1 ((τ * (γ * φ)⁻¹)⁻¹ * τ) (mul_mem (inv_mem hc) hmem) φ⁻¹
    (inv_mem hφ) (by group)

theorem Separated.not_isGraph_of_isField (hτ : P.IsField τ) : ¬ P.IsGraph τ := by
  intro hτ'
  obtain ⟨φ, hφ, -, hc⟩ := hP.exists_mul_inv_mem_of_isField hτ
  obtain ⟨γ, hγ, hγ1, hc'⟩ := hP.exists_mul_inv_mem_of_isGraph hτ'
  exact hP.graph_out γ hγ hγ1 ((τ * γ⁻¹)⁻¹ * (τ * φ⁻¹)) (mul_mem (inv_mem hc') hc) φ hφ
    (by group)

theorem Separated.not_isGraphField_of_isField (hτ : P.IsField τ) : ¬ P.IsGraphField τ := by
  intro hτ'
  obtain ⟨φ', hφ', -, hc⟩ := hP.exists_mul_inv_mem_of_isField hτ
  obtain ⟨γ, hγ, hγ1, φ, hφ, -, hc'⟩ := hP.exists_mul_inv_mem_of_isGraphField hτ'
  exact hP.graph_out γ hγ hγ1 ((τ * (γ * φ)⁻¹)⁻¹ * (τ * φ'⁻¹)) (mul_mem (inv_mem hc') hc)
    (φ' * φ⁻¹) (mul_mem hφ' (inv_mem hφ)) (by group)

theorem Separated.not_isGraphField_of_isGraph (hτ : P.IsGraph τ) : ¬ P.IsGraphField τ := by
  intro hτ'
  obtain ⟨γ, hγ, -, hc⟩ := hP.exists_mul_inv_mem_of_isGraph hτ
  obtain ⟨γ', hγ', -, φ, hφ, hφ1, hc'⟩ := hP.exists_mul_inv_mem_of_isGraphField hτ'
  exact hP.graph_graphField γ hγ γ' hγ' φ hφ hφ1 ((τ * γ⁻¹)⁻¹ * (τ * (γ' * φ)⁻¹))
    (mul_mem (inv_mem hc) hc') (by group)

theorem Separated.not_mem_inndiag_of_hasKind {k : AutKind} (hk : P.HasKind τ k)
    (h1 : k ≠ .inner) (h2 : k ≠ .diagonal) : τ ∉ P.inndiag := by
  cases k with
  | inner => exact absurd rfl h1
  | diagonal => exact absurd rfl h2
  | field => exact hP.not_mem_inndiag_of_isField hk
  | graph => exact hP.not_mem_inndiag_of_isGraph hk
  | graphField => exact hP.not_mem_inndiag_of_isGraphField hk

theorem Separated.not_isInnerAut_of_hasKind {k : AutKind} (hk : P.HasKind τ k)
    (h1 : k ≠ .inner) : ¬ IsInnerAut τ := by
  intro hin
  by_cases h2 : k = .diagonal
  · subst h2
    exact hk.2 hin
  · exact hP.not_mem_inndiag_of_hasKind hk h1 h2 (P.inn_le hin)

theorem Separated.hasKind_unique {k₁ k₂ : AutKind} (h₁ : P.HasKind τ k₁)
    (h₂ : P.HasKind τ k₂) : k₁ = k₂ := by
  have hI : ∀ {k : AutKind}, P.HasKind τ k → (k = .inner ∨ k = .diagonal) → τ ∈ P.inndiag := by
    rintro k hk (rfl | rfl)
    · exact P.inn_le hk
    · exact hk.1
  cases k₁ <;> cases k₂ <;> first
    | rfl
    | exact absurd (hI h₁ (by decide)) (hP.not_mem_inndiag_of_hasKind h₂ (by decide) (by decide))
    | exact absurd (hI h₂ (by decide)) (hP.not_mem_inndiag_of_hasKind h₁ (by decide) (by decide))
    | exact absurd h₁ h₂.2
    | exact absurd h₂ h₁.2
    | exact absurd h₂ (hP.not_isGraph_of_isField h₁)
    | exact absurd h₁ (hP.not_isGraph_of_isField h₂)
    | exact absurd h₂ (hP.not_isGraphField_of_isField h₁)
    | exact absurd h₁ (hP.not_isGraphField_of_isField h₂)
    | exact absurd h₂ (hP.not_isGraphField_of_isGraph h₁)
    | exact absurd h₁ (hP.not_isGraphField_of_isGraph h₂)

end Cosets

end PinnedAut

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem InducesKind.unique {M : Type*} [Group M] {P : PinnedAut M} (hP : P.Separated)
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* M} {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKind L P e x k₁) (h₂ : InducesKind L P e x k₂) : k₁ = k₂ := by
  obtain ⟨hx, h₁⟩ := h₁
  obtain ⟨hx', h₂⟩ := h₂
  exact hP.hasKind_unique h₁ h₂

theorem InducesKind.inducesOuterTheta {M : Type*} [Group M] {P : PinnedAut M}
    (hP : P.Separated) {e : L ⧸ aschbacherSolvableCore 3 L ≃* M} {x : G} {k : AutKind}
    (h : InducesKind L P e x k) (hk : k ≠ .inner) : InducesOuterTheta x L := by
  obtain ⟨hx, h⟩ := h
  exact (not_isInnerAut_inducedAutHom_iff L e hx).mp (hP.not_isInnerAut_of_hasKind h hk)

end Induced

end CFSG.RankThree.PartTwo.KFacts
