module

public import CFSG.RankThree.PartOne.S12.ReflSet
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

open Module LinearMap

section HessianAlgebra

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem ReflData.root_smul (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V} {r r' : V} {φ φ' : V →ₗ[K] K}
    (d : ReflData T r φ) (d' : ReflData T r' φ') : ∃ l : K, r = l • r' := by
  refine ⟨φ' ((2 : K)⁻¹ • r), ?_⟩
  have h1 : T ((2 : K)⁻¹ • r) = (2 : K)⁻¹ • r - φ ((2 : K)⁻¹ • r) • r := d.apply _
  have h1' : φ ((2 : K)⁻¹ • r) = 1 := by
    rw [map_smul, d.pair, smul_eq_mul, inv_mul_cancel₀ h2]
  rw [h1', one_smul] at h1
  have h2' : T ((2 : K)⁻¹ • r) = (2 : K)⁻¹ • r - φ' ((2 : K)⁻¹ • r) • r' := d'.apply _
  have E : (2 : K)⁻¹ • r - r = (2 : K)⁻¹ • r - φ' ((2 : K)⁻¹ • r) • r' := h1.symm.trans h2'
  calc r = (2 : K)⁻¹ • r - ((2 : K)⁻¹ • r - r) := by abel
    _ = (2 : K)⁻¹ • r - ((2 : K)⁻¹ • r - φ' ((2 : K)⁻¹ • r) • r') := by rw [E]
    _ = φ' ((2 : K)⁻¹ • r) • r' := by abel

theorem braid_gram_eq_one [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) {T S : V ≃ₗ[K] V} (hT : T ∈ 𝒟) (hS : S ∈ 𝒟)
    (hne : T ≠ S) (hnc : T * S ≠ S * T) {r r' : V} {φ φ' : V →ₗ[K] K}
    (d : ReflData T r φ) (d' : ReflData S r' φ') : φ r' * φ' r = 1 := by
  rcases dichotomy h2 h3 d d' hne (h.ord T hT S hS hne) with ho | hb
  · exact absurd ho (not_orth_of_not_commute d d' hnc)
  · exact hb

theorem hessian_relations [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟)
    (hnc : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → T * S ≠ S * T)
    {T₁ T₂ T₃ : V ≃ₗ[K] V} (h₁ : T₁ ∈ 𝒟) (h₂ : T₂ ∈ 𝒟) (h₃ : T₃ ∈ 𝒟)
    {r₁ r₂ r₃ : V} {φ₁ φ₂ φ₃ : V →ₗ[K] K}
    (d₁ : ReflData T₁ r₁ φ₁) (d₂ : ReflData T₂ r₂ φ₂) (d₃ : ReflData T₃ r₃ φ₃)
    (hli : ∀ a b c : K, a • r₁ + b • r₂ + c • r₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    φ₁ r₂ * φ₂ r₁ = 1 ∧ φ₁ r₃ * φ₃ r₁ = 1 ∧ φ₂ r₃ * φ₃ r₂ = 1 ∧
      φ₁ r₂ * φ₂ r₃ * φ₃ r₁ + φ₂ r₁ * φ₁ r₃ * φ₃ r₂ = 1 := by
  have h12 : T₁ ≠ T₂ := by
    intro he
    subst he
    obtain ⟨l, hl⟩ := d₁.root_smul h2 d₂
    have := hli 1 (-l) 0 (by rw [hl]; module)
    exact one_ne_zero this.1
  have h13 : T₁ ≠ T₃ := by
    intro he
    subst he
    obtain ⟨l, hl⟩ := d₁.root_smul h2 d₃
    have := hli 1 0 (-l) (by rw [hl]; module)
    exact one_ne_zero this.1
  have h23 : T₂ ≠ T₃ := by
    intro he
    subst he
    obtain ⟨l, hl⟩ := d₂.root_smul h2 d₃
    have := hli 0 1 (-l) (by rw [hl]; module)
    exact one_ne_zero this.2.1
  have e12 := braid_gram_eq_one h2 h3 h h₁ h₂ h12 (hnc _ h₁ _ h₂ h12) d₁ d₂
  have e13 := braid_gram_eq_one h2 h3 h h₁ h₃ h13 (hnc _ h₁ _ h₃ h13) d₁ d₃
  have e23 := braid_gram_eq_one h2 h3 h h₂ h₃ h23 (hnc _ h₂ _ h₃ h23) d₂ d₃
  have h₁₂ : T₁ * T₂ * T₁⁻¹ ∈ 𝒟 := h.conj T₁ h₁ T₂ h₂
  have d₁₂ := d₂.conj T₁
  have h123 : T₁ * T₂ * T₁⁻¹ ≠ T₃ := by
    intro he
    rw [he] at d₁₂
    obtain ⟨l, hl⟩ := d₁₂.root_smul h2 d₃
    rw [d₁.apply r₂] at hl
    have := hli (-(φ₁ r₂)) 1 (-l) (by
      calc (-(φ₁ r₂)) • r₁ + (1 : K) • r₂ + (-l) • r₃ = (r₂ - φ₁ r₂ • r₁) - l • r₃ := by module
        _ = 0 := by rw [hl]; simp)
    exact one_ne_zero this.2.1
  have e := braid_gram_eq_one h2 h3 h h₁₂ h₃ h123 (hnc _ h₁₂ _ h₃ h123) d₁₂ d₃
  have hinv : ∀ x, T₁ (T₁ x) = x := fun x => by
    have := congrArg (fun f : V ≃ₗ[K] V => f x) d₁.mul_self
    simpa using this
  have hs : ∀ x, T₁.symm x = T₁ x := fun x => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hinv x).symm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, d₁.apply, map_sub, map_smul,
    smul_eq_mul] at e
  refine ⟨e12, e13, e23, ?_⟩
  linear_combination (-1 : K) * e + e23 + (φ₃ r₁ * φ₁ r₃) * e12 + e13

theorem hessian_normalize [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟)
    (hnc : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → T * S ≠ S * T)
    {T₁ T₂ T₃ : V ≃ₗ[K] V} (h₁ : T₁ ∈ 𝒟) (h₂ : T₂ ∈ 𝒟) (h₃ : T₃ ∈ 𝒟)
    {r₁ r₂ r₃ : V} {φ₁ φ₂ φ₃ : V →ₗ[K] K}
    (d₁ : ReflData T₁ r₁ φ₁) (d₂ : ReflData T₂ r₂ φ₂) (d₃ : ReflData T₃ r₃ φ₃)
    (hli : ∀ a b c : K, a • r₁ + b • r₂ + c • r₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ (θ : K) (r₂' r₃' : V) (φ₂' φ₃' : V →ₗ[K] K), θ ^ 2 - θ + 1 = 0 ∧
      ReflData T₂ r₂' φ₂' ∧ ReflData T₃ r₃' φ₃' ∧ LinearIndependent K ![r₁, r₂', r₃'] ∧
      φ₁ r₂' = -1 ∧ φ₂' r₁ = -1 ∧ φ₁ r₃' = -1 ∧ φ₃' r₁ = -1 ∧ φ₂' r₃' = θ ∧
      φ₃' r₂' = 1 - θ := by
  obtain ⟨e12, e13, e23, hθ1⟩ := hessian_relations h2 h3 h hnc h₁ h₂ h₃ d₁ d₂ d₃ hli
  have ha0 : φ₁ r₂ ≠ 0 := left_ne_zero_of_mul_eq_one e12
  have ha'0 : φ₂ r₁ ≠ 0 := right_ne_zero_of_mul_eq_one e12
  have hb0 : φ₁ r₃ ≠ 0 := left_ne_zero_of_mul_eq_one e13
  have hb'0 : φ₃ r₁ ≠ 0 := right_ne_zero_of_mul_eq_one e13
  have hθθ : (φ₁ r₂ * φ₂ r₃ * φ₃ r₁) * (φ₂ r₁ * φ₁ r₃ * φ₃ r₂) = 1 := by
    linear_combination (φ₁ r₃ * φ₃ r₁ * φ₂ r₃ * φ₃ r₂) * e12 + (φ₂ r₃ * φ₃ r₂) * e13 + e23
  have hθ : (φ₁ r₂ * φ₂ r₃ * φ₃ r₁) ^ 2 - (φ₁ r₂ * φ₂ r₃ * φ₃ r₁) + 1 = 0 := by
    linear_combination (φ₁ r₂ * φ₂ r₃ * φ₃ r₁) * hθ1 - hθθ
  set θ := φ₁ r₂ * φ₂ r₃ * φ₃ r₁ with hθdef
  have d₂' := d₂.rescale (c := -(φ₁ r₂)) (μ := -(φ₂ r₁)) (by linear_combination e12)
  have d₃' := d₃.rescale (c := -(φ₁ r₃)) (μ := -(φ₃ r₁)) (by linear_combination e13)
  have hli' : LinearIndependent K ![r₁, (-(φ₂ r₁)) • r₂, (-(φ₃ r₁)) • r₃] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_smul] at hg
    obtain ⟨g0, g1, g2⟩ := hli (g 0) (g 1 * -(φ₂ r₁)) (g 2 * -(φ₃ r₁)) (by
      rw [← hg])
    have g1' : g 1 = 0 := by
      rcases mul_eq_zero.1 g1 with h | h
      · exact h
      · exact absurd (neg_eq_zero.1 h) ha'0
    have g2' : g 2 = 0 := by
      rcases mul_eq_zero.1 g2 with h | h
      · exact h
      · exact absurd (neg_eq_zero.1 h) hb'0
    intro i
    fin_cases i
    · exact g0
    · exact g1'
    · exact g2'
  refine ⟨θ, (-(φ₂ r₁)) • r₂, (-(φ₃ r₁)) • r₃, (-(φ₁ r₂)) • φ₂, (-(φ₁ r₃)) • φ₃, hθ, d₂', d₃',
    hli', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, smul_eq_mul]; linear_combination (-1 : K) * e12
  · simp only [LinearMap.smul_apply, smul_eq_mul]; linear_combination (-1 : K) * e12
  · rw [map_smul, smul_eq_mul]; linear_combination (-1 : K) * e13
  · simp only [LinearMap.smul_apply, smul_eq_mul]; linear_combination (-1 : K) * e13
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hθdef]; ring
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; linear_combination hθ1

theorem exists_root_not_mem {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hU : Uspan 𝒟 = ⊤)
    (W : Submodule K V) (hW : W ≠ ⊤) :
    ∃ T ∈ 𝒟, ∃ (r : V) (φ : V →ₗ[K] K), ReflData T r φ ∧ r ∉ W := by
  by_contra hcon
  push Not at hcon
  apply hW
  rw [eq_top_iff, ← hU]
  apply Submodule.span_le.2
  rintro x ⟨T, hT, y, rfl⟩
  obtain ⟨r, φ, hd⟩ := h.refl T hT
  rw [hd.nop_apply]
  exact W.smul_mem _ (hcon T hT r φ hd)

theorem exists_hessian_triple [FiniteDimensional K V] (hdim : finrank K V = 3)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hU : Uspan 𝒟 = ⊤) :
    ∃ (T₁ T₂ T₃ : V ≃ₗ[K] V) (r₁ r₂ r₃ : V) (φ₁ φ₂ φ₃ : V →ₗ[K] K), T₁ ∈ 𝒟 ∧ T₂ ∈ 𝒟 ∧ T₃ ∈ 𝒟 ∧
      ReflData T₁ r₁ φ₁ ∧ ReflData T₂ r₂ φ₂ ∧ ReflData T₃ r₃ φ₃ ∧
      ∀ a b c : K, a • r₁ + b • r₂ + c • r₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨T₁, h₁, r₁, φ₁, d₁, hr₁⟩ := exists_root_not_mem h hU (⊥ : Submodule K V) bot_ne_top
  have hW1 : Submodule.span K ({r₁} : Set V) ≠ ⊤ := by
    intro hb
    have h1 : finrank K (Submodule.span K ({r₁} : Set V)) ≤ 1 := by
      have := finrank_span_finset_le_card (R := K) ({r₁} : Finset V)
      rw [Finset.coe_singleton] at this
      exact this.trans (Finset.card_singleton r₁).le
    rw [hb, finrank_top, hdim] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨T₂, h₂, r₂, φ₂, d₂, hr₂⟩ := exists_root_not_mem h hU _ hW1
  have hW2 : Submodule.span K ({r₁, r₂} : Set V) ≠ ⊤ := by
    intro hb
    have h1 : finrank K (Submodule.span K ({r₁, r₂} : Set V)) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({r₁, r₂} : Finset V)
      rw [Finset.coe_pair] at this
      exact this.trans Finset.card_le_two
    rw [hb, finrank_top, hdim] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨T₃, h₃, r₃, φ₃, d₃, hr₃⟩ := exists_root_not_mem h hU _ hW2
  have hli : ∀ a b c : K, a • r₁ + b • r₂ + c • r₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c habc
    have hc : c = 0 := by
      by_contra hc0
      apply hr₃
      have : r₃ = (-c⁻¹ * a) • r₁ + (-c⁻¹ * b) • r₂ := by
        have : c • r₃ = -(a • r₁ + b • r₂) := by
          calc c • r₃ = (a • r₁ + b • r₂ + c • r₃) - (a • r₁ + b • r₂) := by abel
            _ = -(a • r₁ + b • r₂) := by rw [habc]; simp
        calc r₃ = c⁻¹ • (c • r₃) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
          _ = c⁻¹ • (-(a • r₁ + b • r₂)) := by rw [this]
          _ = (-c⁻¹ * a) • r₁ + (-c⁻¹ * b) • r₂ := by module
      rw [this]
      exact Submodule.mem_span_pair.2 ⟨-c⁻¹ * a, -c⁻¹ * b, rfl⟩
    subst hc
    have hb : b = 0 := by
      by_contra hb0
      apply hr₂
      have : r₂ = (-b⁻¹ * a) • r₁ := by
        have : b • r₂ = -(a • r₁) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          simpa using habc
        calc r₂ = b⁻¹ • (b • r₂) := by rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
          _ = b⁻¹ • (-(a • r₁)) := by rw [this]
          _ = (-b⁻¹ * a) • r₁ := by module
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r₁)
    subst hb
    have ha : a = 0 := by
      by_contra ha0
      apply d₁.ne
      have : a • r₁ = 0 := by simpa using habc
      exact (smul_eq_zero.1 this).resolve_left ha0
    exact ⟨ha, rfl, rfl⟩
  exact ⟨T₁, T₂, T₃, r₁, r₂, r₃, φ₁, φ₂, φ₃, h₁, h₂, h₃, d₁, d₂, d₃, hli⟩

end HessianAlgebra

end ReflF

end CFSG.RankThree.PartOne
