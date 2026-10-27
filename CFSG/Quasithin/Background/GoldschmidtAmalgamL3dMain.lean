module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dDual

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

@[expose] def B3CritDistInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → critDist (A ⊔ B) A B V = 3

@[expose] def B3FourLeCardInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → 4 ≤ critDist (A ⊔ B) A B V → Nat.card (conjClosure V B) = 8

theorem b3CardInput_of_critDist (hb : B3CritDistInput.{u}) : B3CardInput.{u} := by
  intro D _ _ A B z V h
  exact h.card_conjClosure_eq_eight_of_critDist_eq_three (hb D A B z V h)

theorem b3CritDistInput_of_intersection (hi : B3IntersectionInput.{u}) :
    B3CritDistInput.{u} := by
  intro D _ _ A B z V h
  obtain ⟨y, hy, hN⟩ := hi D A B z V h
  exact h.critDist_eq_three_of_inf_conjSub_le hy hN

theorem b3CardInput_of_intersection (hi : B3IntersectionInput.{u}) : B3CardInput.{u} :=
  b3CardInput_of_critDist (b3CritDistInput_of_intersection hi)

end GoldAmL3

end F6

end CFSG.Quasithin
