module

public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Statement

variable {G : Type} [Group G]

@[expose] def C134Case4Min (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      centerOf (c134Q G₀ L) = c134CQ G₀ L ⊔ ⁅centerOf (c134Q G₀ L), L⁆ ∧
      c134CQ G₀ L ⊓ ⁅centerOf (c134Q G₀ L), L⁆ = ⊥ ∧
      IsSumOfNaturalModulesVia L ⁅centerOf (c134Q G₀ L), L⁆ ⊥ α false 1 ∧
      (∃ A₃ A₄ : Subgroup G,
        IsSumOfNaturalModulesVia L A₃ (centerOf (c134Q G₀ L)) α true 1 ∧
        IsSumOfNaturalModulesVia L A₄ A₃ α true 2 ∧
        IsSumOfNaturalModulesVia L (c134Q G₀ L) A₄ α false 2) ∧
      c134CQ G₀ L ≠ ⊥) ∧
    C134NotCentralizerCore G₀ R

@[expose] def IsC134CaseM (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  match i with
  | 1 => IsC134Case1 G₀ R L
  | 2 => IsC134Case2 G₀ R L
  | 3 => IsC134Case3 G₀ R L
  | 4 => C134Case4Min G₀ R L
  | 5 => IsC134Case5 G₀ R L
  | _ => False

end Statement

@[expose] def C134L32CorrM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)), Fintype.card F = 2 ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseM i G₀ R L

section FromCorr

variable {G : Type} [Group G]

theorem C134Case4Min.of_corr {G₀ R L : Subgroup G}
    (h : C134CorrLocal.IsC134Case4Corr G₀ R L) : C134Case4Min G₀ R L := by
  obtain ⟨⟨n, F, i₁, i₂, α, hFc, hα, hE, hZQ, hCU, hU, hΦ, hC, hVC⟩, hN⟩ := h
  refine ⟨⟨n, F, i₁, i₂, α, hFc, hα, hZQ, hCU, hU, ⟨_, _, hΦ, hC, hVC⟩, ?_⟩, hN⟩
  obtain ⟨e⟩ := hE
  have hn : n ≠ 0 := by
    rintro rfl
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rw [hFc] at h2
    norm_num at h2
  intro hbot
  have hcard : Nat.card ↥(c134CQ G₀ L) = 2 ^ (2 * n) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  rw [hbot, Subgroup.card_bot] at hcard
  have : 2 ^ (2 * n) ≠ 1 := (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  exact this hcard.symm

theorem IsC134CaseM.of_corr {i : ℕ} {G₀ R L : Subgroup G}
    (h : C134CorrLocal.IsC134CaseCorr i G₀ R L) : IsC134CaseM i G₀ R L := by
  match i, h with
  | 1, h => exact h
  | 2, h => exact h
  | 3, h => exact h
  | 4, h => exact C134Case4Min.of_corr h
  | 5, h => exact h

end FromCorr

end CFSG.Quasithin
