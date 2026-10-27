module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Core
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c1610_exists_mul_of_mem_sup {A : Type*} [Group A] {H K : Subgroup A}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : A} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ h ∈ H, ∃ k ∈ K, h * k = x) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, K.one_mem, mul_one x⟩
    · exact ⟨1, H.one_mem, x, hx, one_mul x⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    have h21 := hc h₂ hh₂ k₁ hk₁
    calc h₁ * h₂ * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
      _ = h₁ * (k₁ * h₂) * k₂ := by rw [h21]
      _ = h₁ * k₁ * (h₂ * k₂) := by group
  · rintro _ _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    have hhk := hc h hh k hk
    calc h⁻¹ * k⁻¹ = (k * h)⁻¹ := by group
      _ = (h * k)⁻¹ := by rw [hhk]

theorem s16c1610_eq_of_direct_of_centralizer {A : Type} [Group A] {Mb Kb L₀ Lb : Subgroup A}
    (hKdef : Kb = Mb ⊓ centralizer (Lb : Set A)) (hLM : Lb ≤ Mb) (hK : IsSym ↥Kb 3)
    (hdir : IsInternalDirect Kb L₀ Mb) [Finite L₀] (hcard : Nat.card Lb = Nat.card L₀) :
    Lb = L₀ := by
  obtain ⟨hcomm, -, hsup⟩ := hdir
  have hKL : ∀ k ∈ Kb, ∀ l ∈ L₀, k * l = l * k := fun k hk l hl =>
    ((Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hk)) l hl).symm
  have hKLb : ∀ k ∈ Kb, ∀ l ∈ Lb, k * l = l * k := fun k hk l hl => by
    have hk' : k ∈ Mb ⊓ centralizer (Lb : Set A) := hKdef ▸ hk
    exact (Subgroup.mem_centralizer_iff.1 hk'.2 l hl).symm
  have hle : Lb ≤ L₀ := by
    intro x hx
    obtain ⟨κ, hκ, ℓ, hℓ, hkl⟩ := s16c1610_exists_mul_of_mem_sup hKL (hsup ▸ hLM hx)
    have hκeq : κ = x * ℓ⁻¹ := by rw [← hkl]; group
    have hcen : ∀ k' : ↥Kb, (⟨κ, hκ⟩ : ↥Kb) * k' = k' * ⟨κ, hκ⟩ := by
      intro k'
      have hc1 : Commute (k' : A) ℓ := hKL k' k'.2 ℓ hℓ
      have hc2 : Commute (k' : A) x := hKLb k' k'.2 x hx
      have hc3 : Commute (k' : A) κ := by
        rw [hκeq]
        exact hc2.mul_right hc1.inv_right
      exact Subtype.ext hc3.symm.eq
    obtain ⟨e⟩ := hK
    have h1 : e ⟨κ, hκ⟩ = 1 := by
      refine CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => ?_
      have := congrArg e (hcen (e.symm τ))
      simpa using this
    have hκ1 : κ = 1 := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    rw [hκ1, one_mul] at hkl
    exact hkl ▸ hℓ
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem s16c1610_exists_normal_three_of_direct {A : Type} [Group A] {Kb Lb Mb : Subgroup A}
    (hK : IsSym ↥Kb 3) (hdir : IsInternalDirect Kb Lb Mb) :
    ∃ X : Subgroup A, X ≤ Mb ∧ Nat.card X = 3 ∧ ∀ m ∈ Mb, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
  obtain ⟨hcomm, -, hsup⟩ := hdir
  have hKc : Kb ≤ centralizer (Lb : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  obtain ⟨X, hXK, hXcard, hXnK⟩ := s16c1610_a3_of_isSym_three hK
  have hKM : Kb ≤ Mb := hsup ▸ le_sup_left
  refine ⟨X, hXK.trans hKM, hXcard, ?_⟩
  have hle : Mb ≤ Subgroup.normalizer (X : Set A) := by
    rw [← hsup]
    refine sup_le (Subgroup.le_normalizer_iff.2 hXnK) (Subgroup.le_normalizer_iff.2 ?_)
    intro l hl x hx
    have hlx : l * x * l⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.1 (hKc (hXK hx))) l hl
    rw [hlx]
    exact hx
  exact Subgroup.le_normalizer_iff.1 hle

theorem s16c1610_card_gl_two_three :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [s16c1610_card_GL_two]
  decide

theorem s16c1610_card_gl_two_four :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [s16c1610_card_GL_two]
  decide

theorem s16c1610_not_dvd_card_tensor {m : ℕ} (hm3 : 3 ≤ m) (hm4 : m ≤ 4) :
    ¬ 3 ^ m ∣ 6 * Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
  interval_cases m
  · rw [s16c1610_card_gl_two_three]
    decide
  · rw [s16c1610_card_gl_two_four]
    decide

theorem s16c1610_not_isCyclic_of_isElemAbelian {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    {E : Subgroup A} (hE : IsElemAbelian p E) (hcard : p < Nat.card E) : ¬ IsCyclic ↥E := by
  intro hcyc
  have hexp : ∀ b : E, b ^ p = 1 := fun b => Subtype.ext (hE.2 b b.2)
  have h1 : Monoid.exponent E ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  have h2 : Nat.card E ≤ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
