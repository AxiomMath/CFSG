module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Five
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Norm
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YNA

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

@[expose] def B5CardInputNoAC : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → NoACentral A B → critDist (A ⊔ B) A B V = 5 →
      Nat.card (conjClosure V B) = 8

theorem b5CardInputNoAC : B5CardInputNoAC.{u} := by
  intro D _ _ A B z V h hA hb
  rcases h.card_conjClosure_eq with h8 | h16
  · exact h8
  · exact (h.false_of_sixteen_five h16 hb (h.hF_of_noACentral hA)
      (h.I1_of_noACentral hA h16)).elim

end GoldAmL3

end F6

end CFSG.Quasithin
