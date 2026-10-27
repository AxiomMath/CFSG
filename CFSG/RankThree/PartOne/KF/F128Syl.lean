module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly (evenRank)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.RankThree.PartOne.K1214 (SylowShape)

@[expose] def KF128SylTag (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → evenRank J ≤ 3 →
    ∀ (T : Type) [Group T] [Finite T] (π : J →* T), Function.Surjective π →
      π.ker ≤ Subgroup.center J →
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ¬ p ∣ Nat.card π.ker → LocalRankLeTwo p T →
    ∀ n f₀ : ℕ, 1 ≤ f₀ → LieModel T t n 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixModel t n f₀ α →
      FixedFacts p α → 2 ≤ CFSG.pRank p T →
      ∃ e : ℕ, 2 ≤ e ∧ SylowShape p 2 e T ∧ SylowShape p 2 (e - 1) ↥(fixRes α)

@[expose] def KF128Syl : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → evenRank J ≤ 3 →
    ∀ (T : Type) [Group T] [Finite T] (π : J →* T), Function.Surjective π →
      π.ker ≤ Subgroup.center J →
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ¬ p ∣ Nat.card π.ker → LocalRankLeTwo p T →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α → FixedFacts p α →
      2 ≤ CFSG.pRank p T →
      ∃ e : ℕ, 2 ≤ e ∧ SylowShape p 2 e T ∧ SylowShape p 2 (e - 1) ↥(fixRes α)

theorem kf128Syl_of_tags (h : ∀ t : StatedLieTag, KF128SylTag t) : KF128Syl := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hZ hLR2 α hαp hinn hLRA hF hrk
  obtain ⟨t, n, f₀, hf₀, hM, hX⟩ := hF.fieldAutT
  exact h t J hq he T π hπ hker p hp hp5 hZ hLR2 n f₀ hf₀ hM α hαp hinn hLRA hX hF hrk

end CFSG.RankThree.PartOne
