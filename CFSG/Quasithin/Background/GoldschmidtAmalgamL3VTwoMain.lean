module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VEven
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoBR
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoBi
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RProps
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XMain

public section

universe u

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIIConfig V m p)

include c

theorem false_of_typeII (h : GoldHyp3 A B z V) (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v →
    Vv V v ≤ ballStab 1 (p (m - 1))) : False := by
  by_cases hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)
  · exact c.false_of_Bi h hBi
  · exact c.false_of_BR h hgood hBi

end TypeIIConfig

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_typeII {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 8 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hp0 : vtype (p 0) = false)
    (hcrit : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)))
    (hgood : ∀ v, (graph (A ⊔ B) A B).Adj (p 0) v → Vv V v ≤ ballStab 1 (p (m - 1)))
    (hII : ¬ Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) : False :=
  TypeIIConfig.false_of_typeII (m := m) (p := p) ⟨hU, hb, hm, hev, hp, hp0, hcrit, hII⟩ h hgood

theorem false_of_odd_critDist (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 8 ≤ m) (hev : Even m) : False := by
  obtain ⟨p, hp, hp0, hcrit, hgood, hII⟩ := h.exists_good_typeII hU hb (by omega) hev
  exact h.false_of_typeII hU hb hm hev hp hp0 hcrit hgood hII

theorem false_of_nine_le_critDist (hU : Nat.card (conjClosure V B) = 8)
    (hb : 9 ≤ critDist (A ⊔ B) A B V) : False := by
  obtain ⟨m, hm⟩ : ∃ m, critDist (A ⊔ B) A B V = m + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  rcases Nat.even_or_odd m with hev | hodd
  · exact h.false_of_odd_critDist hU hm (by omega) hev
  · exact h.false_of_even_critDist hU hm (by omega) hodd

end GoldHyp3

theorem b9Input : B9Input.{u} := fun _ _ _ _ _ _ _ hV hU hle =>
  hV.false_of_nine_le_critDist hU hle

end GoldAmL3

end F6

end CFSG.Quasithin
