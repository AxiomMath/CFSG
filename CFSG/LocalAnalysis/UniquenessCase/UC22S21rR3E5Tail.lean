module

import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HB
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HC
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3h_false_of_third_member {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D)
    (h211 : S21_1 D Ch) (h82 : F08.R82 D) (h8107 : F08.R8107 D) (h847T : R847E3Thin D)
    (h16 : S21_16 D Ch) (h17 : S21_17 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3)
    (hcent : ∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0)
    (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n)
    (hSzP : ∀ Y ∈ calC D.M, (conjSetOf D.M Y).ncard = 2 → ∀ m : ℕ, 2 < m →
      IsSz (Bar2 Y) m → False)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    {L' : Subgroup G} (hL' : L' ∈ calC D.M) (h₁ : L' ≠ L) (h₂ : L' ≠ K) : False := by
  have h3 := uc22r3h_not_three_dvd_card h82 he h1930 c hn3 hpow hL hK hne hset hL2 hL' h₁ h₂
  obtain ⟨a, hSz'⟩ := uc22r3h_isSz_of_not_three_dvd h16 h1930 c hL' h3
  rcases h17 h1930 c L' hL' with hN | ⟨hc2', m, hm, hS'⟩ | ⟨-, -, hc3, -⟩
  · exact uc22r3h_false_of_normal_sz hSg h13 h211 h8107 h847T h1930 c he hcent hL hK hne
      hset hL2 hL' h₁ h₂
      (uc22p21j_normal_of_conjClosure_eq (PartTwo.s13_le_of_mem_calC hL') hN) hSz'
  · rcases hS' with hL2' | hSz''
    · exact h3 (PartTwo.S17.three_dvd_card_of_bar_isL2Even hL2')
    · exact hSzP L' hL' hc2' m hm hSz''
  · rw [hc3] at hpow
    exact uc22s21ru4e_not_isPowTwo_three hpow

end CFSG.LocalAnalysis.UniquenessCase.UC22
