module

public import CFSG.Quasithin.Recognition.SzVBOddL24Five

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem not_odd_le_five_L24 (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) :
    critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) ≠ 3 ∧
      critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2) ≠ 5 :=
  ⟨critDist_ne_three hRO h hL, critDist_ne_five hRO h hL⟩

end CFSG.Quasithin.SzVB
