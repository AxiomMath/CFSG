module

public import CFSG.RankThree.PartOne.S11d.PSULow

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

@[expose] def ThreeCompAL (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) → LowRank t n →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      ∀ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D →
        (∀ g ∈ D, α g ∈ D) →
        (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

theorem ThreeCompT.toAL {t : StatedLieTag} (h : ThreeCompT t) : ThreeCompAL t :=
  fun T _ _ p hp hp5 hLR h2 n f₀ hf₀ hM _ α hαp hαinn hLRA hX x hxp hx1 hαx =>
    (h T p hp hp5 hLR h2 n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx).1

theorem threeCompAL_of_highRank {t : StatedLieTag} (h : ∀ n, ¬ LowRank t n) : ThreeCompAL t :=
  fun _ _ _ _ _ _ _ _ n _ _ _ hlow => (h n hlow).elim

@[expose] def PSUThreeA : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ f₀ : ℕ, 1 ≤ f₀ → LieModel T .PSU 3 2 (p * f₀) →
    p ∣ 2 ^ (p * f₀) + 1 →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel .PSU 3 f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      ∀ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D →
        (∀ g ∈ D, α g ∈ D) →
        (∀ e ∈ D, ¬ ∀ g ∈ D, α g = e * g * e⁻¹) ∧
        (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
          LieModel (↥D ⧸ Subgroup.center ↥D) t' n' 2 (p * f')) ∧
        ∃ t₁ ∈ D, α t₁ = t₁ ∧ ∃ t₂ ∈ D, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
          (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

theorem threeCompAL_PSU_of_survivor (h3 : PSUThreeA) : ThreeCompAL .PSU := by
  intro T _ _ p hp hp5 hLR2 h2 n f₀ hf₀ hM hlow α hαp hαinn hLRA hX x hxp hx1 hαx D hD hDα
  obtain ⟨rfl, hpQ⟩ := psu_low_cases hp hp5 hLR2 h2 hf₀ hM hlow α hαp hαinn hLRA
  exact h3 T p hp hp5 hLR2 h2 f₀ hf₀ hM hpQ α hαp hαinn hLRA hX x hxp hx1 hαx D hD hDα

end CFSG.RankThree.PartOne.TCX
