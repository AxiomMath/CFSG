module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGKGForkSpOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmMinusOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven TableBSymp


theorem ggRealKGThreeRow_spSplit : GGRealKGThreeRow .spSplit := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeSymplectic_rootSL2 hp (by norm_num) hpn hl2 hQ

theorem ggRealKGThreeRow_dSplit : GGRealKGThreeRow .dSplit := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn⟩, hA⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl3 : 3 ≤ l := hlab.2
  have hl4 : 4 ≤ l := by
    by_contra h
    exact hA (Or.inr (Or.inl ⟨rfl, show l = 3 by omega, hpn⟩))
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hpq : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    have : NeZero l := ⟨by omega⟩
    exact ⟨K, inferInstance, inferInstance, hK, hQ', l,
      TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
      ggTorusRootSL2_of_rootDatum hp (fun _ h _ => h) hZ hcp
        (ggKGRootDatum_of_mulEquiv (rPlusEquivStatedOmega K l)
          (ggKGRootDatum_statedOmegaPlus hl4 hp hp2 hpq))⟩

theorem ggRealKGThreeRow_twdSplit_of_uSplit (hU : GGRealKGThreeRow .uSplit) :
    GGRealKGThreeRow .twdSplit := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn⟩, hA⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl2 : 2 ≤ l := hlab.2
  rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
  · exact (hA (Or.inr (Or.inr ⟨rfl, rfl,
      hpn.trans (by simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2)⟩))).elim
  · exact hU 3 ⟨.twA, 3, n⟩ hp ⟨hlab.1, by norm_num, by norm_num⟩ hl
      ⟨rfl, ⟨rfl, hpn, by norm_num⟩, fun h => by
        rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h⟩
  · have hp2 : (3 : ℕ) ≠ 2 := by norm_num
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
      have := charP_two_of_card hK
      obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
      have hpq : 3 ∣ Nat.card K - 1 := by
        rw [hK]
        exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', l - 1,
        TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq (by omega) b c,
        ggTorusRootSL2_of_rootDatum hp (fun _ h _ => h) hZ hcp
          (ggKGRootDatum_of_mulEquiv (rMinusEquivStatedOmega K (l - 1) b c)
            (ggKGRootDatum_statedOmegaMinus (by omega) hp hp2 hpq hbc))⟩

end CFSG.StandardType

end
