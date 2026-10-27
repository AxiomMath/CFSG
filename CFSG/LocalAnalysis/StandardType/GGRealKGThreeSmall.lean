module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGKGForkSmallRow
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealKGThreeRow_small :
    GGRealKGThreeRow .small := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, hs, -⟩ := hs
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨t, l, n⟩ := lab
  rcases hs with ht | ht | ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_G2_all (lab := ⟨.G2, l, n⟩) hp hp2 rfl) Q hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0,
      TypeA.ggTorusLift_zero (ggKGSm_two_dvd_card_chevG2 (K := K)), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of hp hlab rfl (Or.inl rfl)) Q hQ
    have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
    set σ := iterateFrobeniusEquiv K 2 n with hσdef
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    refine ⟨K, i1, i2, hK, hQ', 0,
      TypeA.ggTorusLift_zero (ggKGSm_two_dvd_card_triD4 hlab.1 hK σ hσ), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hlab rfl) Q hQ
    have hn3 : 3 ≤ n := hlab.2.2.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (ggKGSm_two_dvd_card_sz ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · have hn3 : 3 ≤ n := hlab.2.2.2
    obtain ⟨k, hk⟩ := hlab.2.2.1
    have hk' : n = 2 * k + 1 := hk
    have hpn : 3 ∣ 2 ^ n + 1 := by
      rw [hk', pow_succ, pow_mul]
      have h4 : 4 ^ k % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have : (2 ^ 2) ^ k = 4 ^ k := by norm_num
      omega
    have hs3 : LargeEvenSplit 3 ⟨.twF4, l, n⟩ :=
      Or.inr (Or.inl ⟨id, by simp, hpn⟩)
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
        (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds) hp
        hlab rfl hs3) Q hQ
    have ha : 1 ≤ (n - 1) / 2 := by omega
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (ggKGSm_two_dvd_card_twF4 ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  all_goals
    have hn2 : 2 ≤ n := hl.2.1
    have h1 : n = 1 := hlab.2.2
    omega

end CFSG.StandardType

end
