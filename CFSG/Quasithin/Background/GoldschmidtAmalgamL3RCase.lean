module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RInj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem Zv_ne_geo_two {p : ℕ → CosetGeom (A ⊔ B) A B} {n s : ℕ} (hp : IsGeo p n)
    (hs : s + 2 ≤ n) (hv : vtype (p s) = true) : Zv z (p s) ≠ Zv z (p (s + 2)) := by
  have h01 : (graph (A ⊔ B) A B).Adj (p s) (p (s + 1)) := hp.adj (i := s) (by omega)
  have h12 : (graph (A ⊔ B) A B).Adj (p (s + 1)) (p (s + 2)) := hp.adj (i := s + 1) (by omega)
  exact h.Zv_ne_two h01 h12 (vtype_eq_false_of_adj h01 hv) (hp.ne (by omega) hs)

theorem Zv_ne_geo_four {p : ℕ → CosetGeom (A ⊔ B) A B} {n s : ℕ} (hp : IsGeo p n)
    (hs : s + 3 ≤ n) (hv : vtype (p s) = true) {β : CosetGeom (A ⊔ B) A B}
    (hβ : (graph (A ⊔ B) A B).Adj (p (s + 3)) β) : Zv z (p s) ≠ Zv z β := by
  have h01 : (graph (A ⊔ B) A B).Adj (p s) (p (s + 1)) := hp.adj (i := s) (by omega)
  have h12 : (graph (A ⊔ B) A B).Adj (p (s + 1)) (p (s + 2)) := hp.adj (i := s + 1) (by omega)
  have h23 : (graph (A ⊔ B) A B).Adj (p (s + 2)) (p (s + 3)) := hp.adj (i := s + 2) (by omega)
  exact h.Zv_ne_four h01 h12 h23 hβ (vtype_eq_false_of_adj h01 hv) (hp.ne (by omega) (by omega))
    (hp.ne (by omega) (by omega))

theorem Zv_ne_geo_six (hU : Nat.card (conjClosure V B) = 8)
    {p : ℕ → CosetGeom (A ⊔ B) A B} {n s : ℕ} (hp : IsGeo p n)
    (hs : s + 5 ≤ n) (hv : vtype (p s) = true) {β : CosetGeom (A ⊔ B) A B}
    (hβ : (graph (A ⊔ B) A B).Adj (p (s + 5)) β) : Zv z (p s) ≠ Zv z β := by
  have h01 : (graph (A ⊔ B) A B).Adj (p s) (p (s + 1)) := hp.adj (i := s) (by omega)
  have h12 : (graph (A ⊔ B) A B).Adj (p (s + 1)) (p (s + 2)) := hp.adj (i := s + 1) (by omega)
  have h23 : (graph (A ⊔ B) A B).Adj (p (s + 2)) (p (s + 3)) := hp.adj (i := s + 2) (by omega)
  have h34 : (graph (A ⊔ B) A B).Adj (p (s + 3)) (p (s + 4)) := hp.adj (i := s + 3) (by omega)
  have h45 : (graph (A ⊔ B) A B).Adj (p (s + 4)) (p (s + 5)) := hp.adj (i := s + 4) (by omega)
  exact h.Zv_ne_six hU h01 h12 h23 h34 h45 hβ (vtype_eq_false_of_adj h01 hv)
    (hp.ne (by omega) (by omega)) (hp.ne (by omega) (by omega)) (hp.ne (by omega) (by omega))

theorem false_of_critDist_even (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hm : m = 3 ∨ m = 5 ∨ m = 7) (hb : critDist (A ⊔ B) A B V = m + 1) : False := by
  obtain ⟨p, hp0, hp, hcrit⟩ := h.exists_crit_geodesic hb
  have hev : vtype (p (m + 1)) = false :=
    hp.vtype_false_of_even rfl hp0 le_rfl (by rcases hm with rfl | rfl | rfl <;> decide)
  obtain ⟨c, hc1, hc₁, hcm⟩ := h.coincidence_even hb hp hp0 hcrit hev
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hv1 : vtype (p 1) = true := vtype_eq_true_of_adj h01 hv0
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := hp.adj (i := m) (by omega)
  have hvm : vtype (p m) = true := vtype_eq_true_of_adj hmm.symm hev
  have hzz : Zv z (p 1) = Zv z (p m) := h.Zv_eq_of_mem hv1 hvm hc₁ hcm hc1
  rcases hm with rfl | rfl | rfl
  · exact h.Zv_ne_geo_two (s := 1) hp (by omega) hv1 hzz
  · exact h.Zv_ne_geo_four (s := 1) hp (by omega) hv1 (hp.adj (i := 4) (by omega)) hzz
  · exact h.Zv_ne_geo_six hU (s := 1) hp (by omega) hv1 (hp.adj (i := 6) (by omega)) hzz

theorem false_of_critDist_odd_of_I (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hm : m = 4 ∨ m = 6) (hb : critDist (A ⊔ B) A B V = m + 1)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hp0 : p 0 = γ₀ (A ⊔ B) A B)
    (hcrit : ¬ V ≤ ballStab 1 (p (m + 1))) (hI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) :
    False := by
  have hodd : vtype (p (m + 1)) = true :=
    hp.vtype_true_of_odd rfl hp0 le_rfl (by rcases hm with rfl | rfl <;> decide)
  obtain ⟨c, hc1, hc₁, hcm⟩ := h.coincidence_odd_I hU hb hp hp0 hcrit hodd hI
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hv1 : vtype (p 1) = true := vtype_eq_true_of_adj h01 hv0
  have hvm : vtype (p m) = false :=
    hp.vtype_false_of_even rfl hp0 (by omega) (by rcases hm with rfl | rfl <;> decide)
  obtain ⟨β, hβ, hcβ⟩ := h.exists_adj_mem_Zv hvm hcm hc1
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hvm
  have hzz : Zv z (p 1) = Zv z β := h.Zv_eq_of_mem hv1 hβt hc₁ hcβ hc1
  rcases hm with rfl | rfl
  · exact h.Zv_ne_geo_four (s := 1) hp (by omega) hv1 hβ hzz
  · exact h.Zv_ne_geo_six hU (s := 1) hp (by omega) hv1 hβ hzz

theorem false_of_critDist_seven_of_II (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = 6 + 1)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (6 + 1)) (hp0 : p 0 = γ₀ (A ⊔ B) A B)
    {γ : CosetGeom (A ⊔ B) A B} (hγ : (graph (A ⊔ B) A B).Adj (p (6 + 1)) γ)
    (hnot : ¬ Vv V γ ≤ ballStab 1 (p 1)) : False := by
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hodd : vtype (p (6 + 1)) = true := hp.vtype_true_of_odd rfl hp0 le_rfl (by decide)
  obtain ⟨x, hx, w, hw, hc1, hc2, hc6⟩ := h.coincidence_odd_II hU hb (by omega) hp hv0 hodd hγ hnot
  have hv2 : vtype (p 2) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  have hv6 : vtype (p 6) = false := hp.vtype_false_of_even rfl hp0 (by omega) (by decide)
  obtain ⟨β, hβ, hcβ⟩ := h.exists_adj_mem_Zv hv2 hc2 hc1
  obtain ⟨β', hβ', hcβ'⟩ := h.exists_adj_mem_Zv hv6 hc6 hc1
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hv2
  have hβ't : vtype β' = true := vtype_eq_true_of_adj hβ' hv6
  have hzz : Zv z β = Zv z β' := h.Zv_eq_of_mem hβt hβ't hcβ hcβ' hc1
  by_cases h3 : β = p 3
  · subst h3
    exact h.Zv_ne_geo_four (s := 3) hp (by omega) hβt hβ' hzz
  · exact h.Zv_ne_six hU hβ.symm (hp.adj (i := 2) (by omega)) (hp.adj (i := 3) (by omega))
      (hp.adj (i := 4) (by omega)) (hp.adj (i := 5) (by omega)) hβ' hv2 h3
      (hp.ne (by omega) (by omega)) (hp.ne (by omega) (by omega)) hzz

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
