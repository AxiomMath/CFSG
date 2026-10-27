module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YNA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZEven

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_even_critDist_sixteen_of_noACentral (hA : NoACentral A B)
    (hU : Nat.card (conjClosure V B) = 16) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 7 ≤ m) (hmo : Odd m) : False := by
  obtain ⟨p, hp0, hgeo, hnle⟩ := h.exists_crit_geodesic hb
  exact EvenCritG.false_of_even h ⟨hb, hm, hmo, hgeo, hp0, hnle⟩ hU (h.I1_of_noACentral hA hU)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
