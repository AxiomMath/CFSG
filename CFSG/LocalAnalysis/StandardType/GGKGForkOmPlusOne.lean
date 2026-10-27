module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmPlusRoot
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc OrthExcEven

theorem ggKGOneOn_omegaPlus
    : GGKGOneOn fun p lab => lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  obtain ⟨htag, hl4, hpn⟩ := hs
  dsimp only at htag hl4 hpn
  subst htag
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    have : NeZero l := ⟨by omega⟩
    exact ⟨K, inferInstance, inferInstance, hK, hQ', l, TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq
      (by omega),
      ggTorusRootSL2_of_rootDatum hp (fun _ h _ => h) hZ hcp
        (ggKGRootDatum_of_mulEquiv (rPlusEquivStatedOmega K l)
          (ggKGRootDatum_statedOmegaPlus hl4 hp hp2 hpq))⟩

end CFSG.StandardType
