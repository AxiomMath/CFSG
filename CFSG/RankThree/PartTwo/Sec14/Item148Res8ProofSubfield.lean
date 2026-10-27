module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfieldLin
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfieldUni
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Item148Res8

section Steps


theorem kf148SubfieldOver_holds : KF148SubfieldOver := by
  intro Γ _ _ X K H σ n hn hX hind hσ3 hσN hKX hKC hKs hK hKH hHX
  have h0 : 2 ^ (3 * n) % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ (3 * n) := Nat.dvd_of_mod_eq_zero h0
    have := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at this
  rcases (by omega : 2 ^ (3 * n) % 3 = 1 ∨ 2 ^ (3 * n) % 3 = 2) with hq | hq
  · exact subfieldOver_of_linear hn hX hq hind hσ3 hσN hKX hKC hKs hK hKH hHX
  · exact subfieldOver_of_unitary hn hX hq hind hσ3 hσN hKX hKC hKs hK hKH hHX

theorem step148Rank_of_res8_final
    (h133 : Item133)
    (h134 : Item134) (h48 : Sec4.Item4_8) (hFive : Step148RankFive) : Step148Rank :=
  step148Rank_of_res8_kf kf148SubfieldOver_holds h133 h134 h48 hFive

end Steps

end Item148Res8

end CFSG.RankThree.PartTwo.Sec14
