module

public import CFSG.Quasithin.Recognition.SzVBEvenSetting

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem not_isL2Quot_two_of_three {X : Type*} [Group X] [Finite X] (h3 : IsL2Quot 3 X) :
    ¬ IsL2Quot 2 X := by
  intro h2
  have c3 : Nat.card X = 2 ^ 3 * (4 ^ 3 - 1) := IsL2Quot.card (by norm_num) h3
  have c2 : Nat.card X = 2 ^ 2 * (4 ^ 2 - 1) := IsL2Quot.card (by norm_num) h2
  rw [c3] at c2
  norm_num at c2

theorem r1b_vBeta_nonabelian (hRO : RankOneListedFacts.{0})
    (hset : R1SettingLegacyBare K1 L2 S Zs) (hL28 : IsL2Quot 3 (OTwoQuot K1)) :
    ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ := by
  intro hab
  have hne := not_isL2Quot_two_of_three hL28
  have hX : IsBenderQuot 3 (OTwoQuot K1) := Or.inl hL28
  rcases Nat.even_or_odd
      (CosetGeom.critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) with hev | hodd
  · exact SzVB.even_critDist_false_of_setting hRO hset (by norm_num) hX hne hab hev
  · exact SzVB.odd_critDist_false hRO hset hab
      (SzVB.benderLocalFacts_of_setting hRO hset (by norm_num) hX hne) hodd

end CFSG.Quasithin.Background.Harris.R1
