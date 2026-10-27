module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdRoot
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealRootSL2On_three_uNonsplitDvd_ne_five :
    GGRealRootSL2On fun p lab => p = 3 ∧ GGKGRowLabel .uNonsplitDvd p lab ∧ lab.rank ≠ 5 := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn, hpl⟩, h5⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hpl h5
  subst htag
  have hn : 1 ≤ n := hlab.1
  obtain ⟨k, hk⟩ := hpl
  rcases (show l = 2 ∨ 8 ≤ l by omega) with rfl | hl8
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      largeEvenLabelAll_lift_card_lt_unitaryThree_all (lab := ⟨.twA, 2, n⟩)
        hp (by norm_num) hlab rfl rfl Q hQ
    have := (TableBU.unitaryFieldData_of_card hK hn).charP
    refine ⟨K, i1, i2, hK, hQ', 0,
      TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := 3) (f := n) (K := K)
        (by norm_num)), ?_⟩
    intro L' _ _ ψ A hA
    obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hA
    exact absurd h3 (not_le.mpr (hpc L' ψ hψ hker hperf A hAe hAI))
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    refine ⟨K, i1, i2, hK, hQ', l + 1 - 3, ?_, ?_⟩
    · have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
        intro heq
        have := congrArg Prod.fst heq
        simp only at this
        omega
      have hpl' : 3 ∣ l + 1 := ⟨k, hk⟩
      have hrank : ggUnitaryTorusRank 3 (l + 1) = l + 1 - 3 := by
        rw [ggUnitaryTorusRank, if_pos hpl']
      rw [← hrank]
      exact ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpn
    · have hle : (l + 1) / 3 + 2 ≤ max (l + 1 - 3) 3 := by
        rcases le_total (l + 1 - 3) 3 with h | h
        · rw [max_eq_right h]
          omega
        · rw [max_eq_left h]
          omega
      exact ggTorusRootSL2_psu_dvd (K := K) (n := n) (d := l + 1) hK hl.2.1 (by omega)
        hp (by norm_num) hle hpn ⟨k, hk⟩

theorem largeEvenLabelAll_torusRootSL2_four_U63
    {n : ℕ} (hn : 2 ≤ n)
    (hpn : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twA, 5, n⟩ fun R _ I _ => GGTorusRootSL2 3 4 R I := by
  intro Q hQ
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ', ggTorusRootSL2_psu_dvd (K := K) (n := n) (d := 6) hK hn
    (by norm_num) Nat.prime_three (by norm_num) (by norm_num) hpn (by norm_num)⟩

end CFSG.StandardType

end
