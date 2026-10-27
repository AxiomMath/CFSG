module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Red

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

@[expose] def B7NoACInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → 7 ≤ critDist (A ⊔ B) A B V → Nat.card (conjClosure V B) = 16 →
      NoACentral A B

@[expose] def B7I2aInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → NoACentral A B → 7 ≤ critDist (A ⊔ B) A B V →
      Nat.card (conjClosure V B) = 16 → I2aProp A B V

end GoldAmL3

end F6

end CFSG.Quasithin
