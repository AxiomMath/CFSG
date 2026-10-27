module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmMinusRoot
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven

theorem ggKGOneOn_omegaMinus
    : GGKGOneOn fun p lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  obtain ⟨htag, hl4, hpn⟩ := hs
  dsimp only at htag hl4 hpn
  subst htag
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', l - 1,
      TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq (by omega) b c,
      ggTorusRootSL2_of_rootDatum hp (fun _ h _ => h) hZ hcp
        (ggKGRootDatum_of_mulEquiv (rMinusEquivStatedOmega K (l - 1) b c)
          (ggKGRootDatum_statedOmegaMinus (by omega) hp hp2 hpq hbc))⟩

end CFSG.StandardType
