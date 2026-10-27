module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Fin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Lin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Uni
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Exc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Spor

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin

section Main


theorem outThreeOrElemNine_of_a23List {S : Type} [Group S] [Finite S] (h : A23List S) :
    OutThreeOrElemNine S := by
  rcases h with ⟨n, hn5, -, ⟨e⟩⟩ | ⟨p, hp, hp2, hmod⟩ | ⟨⟨f, hf⟩ | hTits⟩ | ⟨n, hn, hm⟩ | hspor
  ·
    exact outThreeOrElemNine_of_alt hn5 e
  ·
    rcases hmod with ⟨f, -, hm⟩ | hm | hm
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
      exact outThreeOrElemNine_of_statedPSL2 e
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
      exact outThreeOrElemNine_of_statedPSL3 e
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      have hq : 2 < p ^ 1 := by
        have := hp.two_le
        rw [pow_one]
        omega
      exact outThreeOrElemNine_of_statedPSU3 hp le_rfl hq hK e
  ·
    rcases hf with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨hf2, hm⟩ | ⟨-, hm⟩ | ⟨hf2, hm⟩ | ⟨hf1, hm⟩ | ⟨-, -, hm⟩ |
      ⟨-, -, hm⟩
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
      exact outThreeOrElemNine_of_statedPSL2 e
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
      exact outThreeOrElemNine_of_statedPSL3 e
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      have hq : 2 < 2 ^ f := by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact outThreeOrElemNine_of_statedPSU3 Nat.prime_two (by omega) hq hK e
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
        rw [← Nat.card_eq_fintype_card, hK])
      exact outThreeOrElemNine_of_statedPSp4Even e
    · exact outThreeOrElemNine_of_g2 hf2 hm
    · exact outThreeOrElemNine_of_triality hf1 hm
    · exact outThreeOrElemNine_of_largeRee hm
    · exact outThreeOrElemNine_of_suzukiModel hm
  ·
    exact outThreeOrElemNine_of_tits hTits
  ·
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
    rcases hn with rfl | rfl
    · exact outThreeOrElemNine_of_statedPSL4 e
    · exact outThreeOrElemNine_of_statedPSL5 e
  ·
    exact outThreeOrElemNine_of_sporadic hspor

theorem input15338Rank1_holds : Input15338Rank1 := by
  intro Y _ _ L₁ B hq hA h1 hBN hB
  exact three_le_pRank_of_rank_one hq h1 hBN hB (outThreeOrElemNine_of_a23List hA)

end Main

end CFSG.Quasithin.SBd19F
