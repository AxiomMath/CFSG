module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S9Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YNAMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RFin
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Rel

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem swapProp_of_noACentral (hA : NoACentral A B) : SwapProp A B :=
  fun {u v w} huv hu hvw hwu => by
    have hv : vtype v = true := vtype_eq_true_of_adj huv hu
    have hnot := h.hF_of_noACentral hA u v w hv huv hvw hwu.symm
    by_contra hcon
    push Not at hcon
    exact hnot fun g hg => hcon g hg.2 hg.1

end GoldHyp3

@[expose] def B7I2aOddInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → NoACentral A B → 7 ≤ critDist (A ⊔ B) A B V →
      Odd (critDist (A ⊔ B) A B V) → Nat.card (conjClosure V B) = 16 → I2aProp A B V

theorem b7I2aInput_of_odd (hOdd : B7I2aOddInput.{u}) : B7I2aInput.{u} := by
  intro D _ _ A B z V h hA hb hU
  obtain ⟨m, hm⟩ : ∃ m, critDist (A ⊔ B) A B V = m + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  rcases Nat.even_or_odd m with hme | hmo
  · exact hOdd D A B z V h hA hb (by rw [hm]; exact hme.add_one) hU
  · obtain ⟨k, hk⟩ := hmo
    exact (h.false_of_even_critDist_sixteen_of_noACentral hA hU hm (by omega) ⟨k, hk⟩).elim

theorem b7CardInput_of_odd (hOdd : B7I2aOddInput.{u}) : B7CardInput.{u} :=
  b7CardInput_of_noACentral_I2a
    (fun D _ _ A B z V h hb hU => b5LeNoACInput D A B z V h (by omega) hU)
    (b7I2aInput_of_odd hOdd)

end GoldAmL3

end F6

end CFSG.Quasithin
