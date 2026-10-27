module

public import CFSG.RankThree.PartOne.S11d.PSULow
public import CFSG.RankThree.PartOne.TCU.ThreeComp

public section

namespace CFSG.RankThree.PartOne.TCX

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Blueprint (LieModel)

@[expose] def PSUThreeSurvivor : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LocalRankLeTwo p T →
    2 ≤ CFSG.pRank p T → ∀ f₀ : ℕ, 1 ≤ f₀ → LieModel T .PSU 3 2 (p * f₀) →
    p ∣ 2 ^ (p * f₀) + 1 →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel .PSU 3 f₀ α →
    ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
      ∀ S : Subgroup T, S ≠ ⊥ → IsPGroup 2 ↥S → (∀ g ∈ S, α g ∈ S) →
        x ∈ Subgroup.normalizer (S : Set T) →
        ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D ∧
          (∀ g ∈ D, α g ∈ D) ∧
          ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
            g ∈ D

theorem threeCompBL_PSU_of_survivor (h3 : PSUThreeSurvivor) : ThreeCompBL .PSU := by
  intro T _ _ p hp hp5 hLR2 h2 n f₀ hf₀ hM hlow α hαp hαinn hLRA hX x hxp hx1 hαx S hS1 hS2 hSα
    hxS
  obtain ⟨rfl, hpQ⟩ := psu_low_cases hp hp5 hLR2 h2 hf₀ hM hlow α hαp hαinn hLRA
  exact h3 T p hp hp5 hLR2 h2 f₀ hf₀ hM hpQ α hαp hαinn hLRA hX x hxp hx1 hαx S hS1 hS2 hSα hxS

theorem threeCompBL_PSU : ThreeCompBL .PSU :=
  threeCompBL_PSU_of_survivor threeCompBL_PSU_three

end CFSG.RankThree.PartOne.TCX
