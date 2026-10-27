module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dMain

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

namespace GoldHyp3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem critDist_ne_six' (h : GoldHyp3 A B z V) : critDist (A ⊔ B) A B V ≠ 6 := by
  intro hb
  have hb' : critDist (A ⊔ B) A B V = 5 + 1 := hb
  obtain ⟨p, hp0, hp, hcrit⟩ := h.exists_crit_geodesic hb'
  have hev : vtype (p (5 + 1)) = false := hp.vtype_false_of_even rfl hp0 le_rfl (by decide)
  obtain ⟨c, hc1, hc₁, hcm⟩ := h.coincidence_even hb' hp hp0 hcrit hev
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hv1 : vtype (p 1) = true := vtype_eq_true_of_adj h01 hv0
  have hmm : (graph (A ⊔ B) A B).Adj (p 5) (p (5 + 1)) := hp.adj (i := 5) (by omega)
  have hvm : vtype (p 5) = true := vtype_eq_true_of_adj hmm.symm hev
  have hzz : Zv z (p 1) = Zv z (p 5) := h.Zv_eq_of_mem hv1 hvm hc₁ hcm hc1
  exact h.Zv_ne_geo_four (s := 1) hp (by omega) hv1 (hp.adj (i := 4) (by omega)) hzz

end GoldHyp3

@[expose] def B5CardInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → critDist (A ⊔ B) A B V = 5 → Nat.card (conjClosure V B) = 8

@[expose] def B7CardInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → 7 ≤ critDist (A ⊔ B) A B V → Nat.card (conjClosure V B) = 8

theorem b3FourLeCardInput_of_five_seven (h5 : B5CardInput.{u}) (h7 : B7CardInput.{u}) :
    B3FourLeCardInput.{u} := by
  intro D _ _ A B z V h h4
  have hne4 := h.critDist_ne_four
  have hne6 := h.critDist_ne_six'
  by_cases hb5 : critDist (A ⊔ B) A B V = 5
  · exact h5 D A B z V h hb5
  · exact h7 D A B z V h (by omega)

end GoldAmL3

end F6

end CFSG.Quasithin
