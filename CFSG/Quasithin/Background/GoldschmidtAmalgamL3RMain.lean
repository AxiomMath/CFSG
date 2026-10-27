module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RProps
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dMain
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3KGap

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

theorem b5Input_of_b5SymInput (h5 : B5SymInput.{u}) : B5Input.{u} := by
  intro D _ _ A B z V h hU hb
  have hb' : critDist (A ⊔ B) A B V = 4 + 1 := hb
  obtain ⟨p, hp0, hp, hcrit⟩ := h.exists_crit_geodesic hb'
  have hvodd : vtype (p (4 + 1)) = true := hp.vtype_true_of_odd rfl hp0 le_rfl (by decide)
  by_cases hII : ∃ γ, (graph (A ⊔ B) A B).Adj (p (4 + 1)) γ ∧ ¬ Vv V γ ≤ ballStab 1 (p 1)
  · obtain ⟨γ, hγ, hnot⟩ := hII
    exact h5 D A B z V h hU hb p γ ⟨hp0, hp, hcrit, hγ, hnot⟩
  · push Not at hII
    exact h.false_of_critDist_odd_of_I hU (Or.inl rfl) hb' hp hp0 hcrit
      ((Vv_B_le_iff hvodd).mpr hII)

theorem b3NoFourInput_of_reduced (h8 : B3FourLeCardInput.{u}) (h5 : B5SymInput.{u})
    (h9 : B9Input.{u}) : GoldAmL3K.B3NoFourInput.{u} := by
  intro D _ _ A B z V h h4
  have hU := h8 D A B z V h h4
  by_cases hge : 9 ≤ critDist (A ⊔ B) A B V
  · exact h9 D A B z V h hU hge
  obtain ⟨m, hm⟩ : ∃ m, critDist (A ⊔ B) A B V = m + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  by_cases hev : m = 3 ∨ m = 5 ∨ m = 7
  · exact h.false_of_critDist_even hU hev hm
  have hodd : m = 4 ∨ m = 6 := by omega
  rcases hodd with rfl | rfl
  · exact b5Input_of_b5SymInput h5 D A B z V h hU hm
  · obtain ⟨p, hp0, hp, hcrit⟩ := h.exists_crit_geodesic hm
    have hvodd : vtype (p (6 + 1)) = true := hp.vtype_true_of_odd rfl hp0 le_rfl (by decide)
    by_cases hII : ∃ γ, (graph (A ⊔ B) A B).Adj (p (6 + 1)) γ ∧ ¬ Vv V γ ≤ ballStab 1 (p 1)
    · obtain ⟨γ, hγ, hnot⟩ := hII
      exact h.false_of_critDist_seven_of_II hU hm hp hp0 hγ hnot
    · push Not at hII
      exact h.false_of_critDist_odd_of_I hU (Or.inr rfl) hm hp hp0 hcrit
        ((Vv_B_le_iff hvodd).mpr hII)

namespace GoldHyp3

theorem symConfigFive_data {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D}
    {V : Subgroup D} (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = 5) {p : ℕ → CosetGeom (A ⊔ B) A B}
    {γ : CosetGeom (A ⊔ B) A B} (hcfg : SymConfigFive A B V p γ) :
    ∃ x ∈ Vv V (p 1), ∃ w ∈ Vv V γ, x * w * x⁻¹ * w⁻¹ ≠ 1 ∧ x * w * x⁻¹ * w⁻¹ ∈ Zv z (p 3) ∧
      x * w * x⁻¹ * w⁻¹ ∈ Vv V (p 2) ⊓ Vv V (p 4) := by
  obtain ⟨hp0, hp, -, hγ, hnot⟩ := hcfg
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hodd : vtype (p (4 + 1)) = true := hp.vtype_true_of_odd rfl hp0 le_rfl (by decide)
  obtain ⟨x, hx, w, hw, hc1, hc⟩ :=
    h.coincidence_odd_II hU (m := 4) hb (by omega) hp hv0 hodd hγ hnot
  have hv2 : vtype (p 2) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have hv4 : vtype (p 4) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  obtain ⟨β, hβ, hcβ⟩ := h.exists_adj_mem_Zv hv2 hc.1 hc1
  obtain ⟨β', hβ', hcβ'⟩ := h.exists_adj_mem_Zv hv4 hc.2 hc1
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hv2
  have hβ't : vtype β' = true := vtype_eq_true_of_adj hβ' hv4
  have hzz : Zv z β = Zv z β' := h.Zv_eq_of_mem hβt hβ't hcβ hcβ' hc1
  have h3 : β = p 3 := by
    by_contra hne
    exact h.Zv_ne_four hβ.symm (hp.adj (i := 2) (by omega)) (hp.adj (i := 3) (by omega)) hβ' hv2
      hne (hp.ne (by omega) (by omega)) hzz
  refine ⟨x, hx, w, hw, hc1, ?_, hc⟩
  rw [← h3]
  exact hcβ

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
