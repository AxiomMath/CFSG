module

public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

@[expose] def ThreeCompB (t : StatedLieTag) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      ∀ S : Subgroup T, S ≠ ⊥ → IsPGroup 2 ↥S → (∀ g ∈ S, α g ∈ S) →
        x ∈ Subgroup.normalizer (S : Set T) →
        ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D ∧
          (∀ g ∈ D, α g ∈ D) ∧
          ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
            g ∈ D

theorem ThreeCompT.toB {t : StatedLieTag} (h : ThreeCompT t) : ThreeCompB t := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM α hαp hαinn hLR hFix x hxp hx1 hαx S hS1 hS2 hSα hSx
  obtain ⟨-, hB⟩ := h T p hp hp5 hrank h2 n f₀ hf₀ hM α hαp hαinn hLR hFix x hxp hx1 hαx
  obtain ⟨D, hD, hDα, -, hDfix⟩ := hB S hS1 hS2 hSα hSx
  exact ⟨D, hD, hDα, hDfix⟩

end CFSG.RankThree.PartOne.TCX
