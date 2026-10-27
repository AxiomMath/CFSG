
module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.C134CorrLocal

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open CFSG.Assembly.LowTwoRank

section Statement

variable {G : Type} [Group G]

@[expose] def IsC134Case4Corr (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsE2 (2 * n) ↥(c134CQ G₀ L) ∧
      centerOf (c134Q G₀ L) = c134CQ G₀ L ⊔ ⁅centerOf (c134Q G₀ L), L⁆ ∧
      c134CQ G₀ L ⊓ ⁅centerOf (c134Q G₀ L), L⁆ = ⊥ ∧
      IsSumOfNaturalModulesVia L ⁅centerOf (c134Q G₀ L), L⁆ ⊥ α false 1 ∧
      IsSumOfNaturalModulesVia L (frattiniIn (c134Q G₀ L)) (centerOf (c134Q G₀ L)) α true 1 ∧
      IsSumOfNaturalModulesVia L
        (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G))
        (frattiniIn (c134Q G₀ L)) α true 2 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L)
        (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) α false 2) ∧
    C134NotCentralizerCore G₀ R

@[expose] def IsC134CaseCorr (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  match i with
  | 1 => IsC134Case1 G₀ R L
  | 2 => IsC134Case2 G₀ R L
  | 3 => IsC134Case3 G₀ R L
  | 4 => IsC134Case4Corr G₀ R L
  | 5 => IsC134Case5 G₀ R L
  | _ => False

theorem IsC134Case4.corr {G₀ R L : Subgroup G} (h : IsC134Case4 G₀ R L) :
    IsC134Case4Corr G₀ R L := by
  obtain ⟨⟨n, F, i₁, i₂, α, hF, hα, hE, -, h₁⟩, hN⟩ := h
  exact ⟨⟨n, F, i₁, i₂, α, hF, hα, hE, h₁⟩, hN⟩

theorem IsC134Case.corr {i : ℕ} {G₀ R L : Subgroup G} (h : IsC134Case i G₀ R L) :
    IsC134CaseCorr i G₀ R L := by
  match i, h with
  | 1, h => exact h
  | 2, h => exact h
  | 3, h => exact h
  | 4, h => exact IsC134Case4.corr h
  | 5, h => exact h

end Statement

end CFSG.Quasithin.C134CorrLocal
