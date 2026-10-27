module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S11d.Facts5

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

@[expose] def ThreeCompT (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      (∀ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D →
        (∀ g ∈ D, α g ∈ D) →
        (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) ∧
      ∀ S : Subgroup T, S ≠ ⊥ → IsPGroup 2 ↥S → (∀ g ∈ S, α g ∈ S) →
        x ∈ Subgroup.normalizer (S : Set T) →
        ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D ∧
          (∀ g ∈ D, α g ∈ D) ∧
          (∀ D' : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D' → D' = D) ∧
          ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D

end CFSG.RankThree.PartOne.TCX
