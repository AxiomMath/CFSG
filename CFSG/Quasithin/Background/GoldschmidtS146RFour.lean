module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatLin
public import CFSG.Quasithin.Background.GoldschmidtS146RLatSp
public import CFSG.Quasithin.Background.GoldschmidtS146RLatG2
public import CFSG.Quasithin.Background.GoldschmidtS146RLatSmall
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.Background.GoldschmidtS146RCases
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.GH74.Orders.LieType
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {X : Type} [Group X]

theorem ordA_one_two_pow {n : ℕ} (hn : 1 ≤ n) : ordA 1 (2 ^ n) = ordL2 n := by
  have hodd : Odd (2 ^ n - 1) := by
    have h := odd_two_pow_pow_sub_one' (n := n) (k := 1) hn le_rfl
    simpa using h
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [ordA_one_eq, hg, Nat.div_one]
  rfl

theorem latShape_of_fourList [Finite X] [IsSimpleGroup X] (h : FourList X) (h7 : ¬ IsAlt 7 X)
    (hM : ¬ IsSporadic .M22 X) (h4 : ¬ IsPSL 4 2 1 X) (h5 : ¬ IsPSL 5 2 1 X)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  rcases h with ⟨n, hn, hX | hX | hX⟩ | ⟨n, hn, hX⟩ | ⟨n, hn, hX⟩ | hX | ⟨n, hn, hX⟩ | hX |
    hX | hX | hX | hX
  · exact LatShape.of_bender (fusionIsBenderGroup_of_shape (Or.inl ⟨n, hX⟩)) hU
  · exact LatShape.of_bender (fusionIsBenderGroup_of_shape (Or.inr (Or.inl ⟨n, hX⟩))) hU
  · exact LatShape.of_bender
      (CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psu_three hn hX) hU
  · by_cases hn2 : 2 ≤ n
    · exact latShape_of_isPSL_three hn2 hX hU
    · have : n = 1 := by omega
      subst this
      exact latShape_of_card_168 (card_of_isPSL_three_two hX) hU
  · exact latShape_of_isPSp_four hn hX hU
  · exact latShape_of_isAlt_six hX hU
  · exact latShape_of_isG2 hn hX hU
  · exact latShape_of_isPSU_three_three hX hU
  · exact absurd hX h4
  · exact absurd hX h5
  · exact absurd hX h7
  · exact absurd hX hM

theorem srcProfile_of_fourList [Finite X] (h : FourList X) (h7 : ¬ IsAlt 7 X)
    (hM : ¬ IsSporadic .M22 X) (h4 : ¬ IsPSL 4 2 1 X) (h5 : ¬ IsPSL 5 2 1 X) :
    SrcProfile (Nat.card X) := by
  rcases h with ⟨n, hn, hX | hX | hX⟩ | ⟨n, hn, hX⟩ | ⟨n, hn, hX⟩ | hX | ⟨n, hn, hX⟩ | hX |
    hX | hX | hX | hX
  · have := card_of_isPSL hX
    rw [show 2 - 1 = 1 from rfl, ordA_one_two_pow (by omega)] at this
    rw [this]
    exact srcProfile_ordL2 hn
  · obtain ⟨-, a, -, -, hcard⟩ := CFSG.GH74.card_of_suzukiModel hX
    rw [hcard]
    exact srcProfile_ordSuzuki hn
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two hX).2.1 rfl
    rw [this]
    exact srcProfile_ordTwistedA_two hn
  · have := card_of_isPSL hX
    rw [show 3 - 1 = 2 from rfl] at this
    rw [this]
    exact srcProfile_ordA_two hn
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two hX).2.2.1 rfl
    rw [this]
    exact srcProfile_ordBC_two hn
  · rw [card_of_isAlt_six hX]
    exact Or.inr (Or.inr (Or.inl rfl))
  · have := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hX).1 rfl
    rw [this]
    exact srcProfile_ordG2 hn
  · have hp := card_of_isPSU_three Nat.prime_three hX
    rw [hp, ordTwistedA_two_eq' 3 (by norm_num)]
    exact srcProfile_6048 |> fun h => by simpa using h
  · exact absurd hX h4
  · exact absurd hX h5
  · exact absurd hX h7
  · exact absurd hX hM

end CFSG.Quasithin.GoldS146R
