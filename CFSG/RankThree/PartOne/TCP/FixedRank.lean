module

public import CFSG.RankThree.PartOne.TCP.Concrete
public import CFSG.RankThree.PartOne.TCP.Config

public section

namespace CFSG.RankThree.PartOne.TCX

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.TCP
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem fixedRankT_PSp : FixedRankT .PSp := by
  intro T _ _ p hp hp5 hrank h2 n f₀ hf₀ hM α hαp hαinn hLR hFix
  obtain ⟨K, _, _, k₀, _, _, hn2, hK, hk₀, ⟨eT⟩, ⟨eF⟩⟩ :=
    psp_concrete hp hp5 hrank hf₀ hM hαp hαinn hLR hFix
  have hp2 : p ≠ 2 := by omega
  have : CharP k₀ 2 := K128.charP_two_of_card_eq_two_pow hk₀
  have hpK : ¬ p ∣ Nat.card K := by
    have : CharP K 2 := K128.charP_two_of_card_eq_two_pow hK
    exact not_dvd_card_of_charTwo hp hp2
  have hpk : ¬ p ∣ Nat.card k₀ := not_dvd_card_of_charTwo hp hp2
  have hQ : Nat.card K = Nat.card k₀ ^ p := by rw [hK, hk₀, ← pow_mul, mul_comm]
  have hrk : 2 ≤ CFSG.pRank p ↥(StatedSp n K) := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT]
    exact h2
  have hbd := blockDim_le_of_two_le_pRank hp hp2 hpK hrk
  rw [orderOf_natCast_pow_prime hp hQ] at hbd
  obtain ⟨R, hRe, hRc, -⟩ := exists_psp_config hp hpk hbd
  have h3 : 2 ≤ CFSG.pRank p ↥(StatedSp n k₀) :=
    CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt R hRe hRc
  rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eF]
  exact h3

end CFSG.RankThree.PartOne.TCX
