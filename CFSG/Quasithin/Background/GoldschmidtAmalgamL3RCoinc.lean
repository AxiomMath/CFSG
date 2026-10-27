module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem IsGeo.vtype_false_of_even {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hG : G₀ = G₁ ⊔ G₂)
    (hp : IsGeo p n) (hp0 : p 0 = γ₀ G₀ G₁ G₂) {i : ℕ} (hi : i ≤ n) (he : Even i) :
    vtype (p i) = false :=
  vtype_eq_false_of_even hG (by rw [← hp0, hp 0 i (Nat.zero_le _) hi]; simpa using he)

theorem IsGeo.vtype_true_of_odd {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hG : G₀ = G₁ ⊔ G₂)
    (hp : IsGeo p n) (hp0 : p 0 = γ₀ G₀ G₁ G₂) {i : ℕ} (hi : i ≤ n) (ho : Odd i) :
    vtype (p i) = true :=
  vtype_eq_true_of_odd hG (by rw [← hp0, hp 0 i (Nat.zero_le _) hi]; simpa using ho)

end CosetGeom

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_crit_geodesic {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1) :
    ∃ p : ℕ → CosetGeom (A ⊔ B) A B, p 0 = γ₀ (A ⊔ B) A B ∧ IsGeo p (m + 1) ∧
      ¬ V ≤ ballStab 1 (p (m + 1)) := by
  obtain ⟨α, hα, hVα⟩ := exists_dist_eq_critDist_not_le (h.gold.amalgamHypV h.natural)
    h.natural.natural.ne_bot
  rw [hb] at hα
  obtain ⟨p, hp0, hpα, hgeo⟩ := exists_geodesic (rfl : A ⊔ B = A ⊔ B) (m + 1) _ _ hα
  refine ⟨p, hp0, hgeo, ?_⟩
  rw [hpα]
  exact hVα

theorem coincidence_even {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hp0 : p 0 = γ₀ (A ⊔ B) A B)
    (hcrit : ¬ V ≤ ballStab 1 (p (m + 1))) (hev : vtype (p (m + 1)) = false) :
    ∃ c : D, c ≠ 1 ∧ c ∈ Zv z (p 1) ∧ c ∈ Zv z (p m) := by
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := hp.adj (i := m) (by omega)
  have hV0 : Vv V (p 0) = V := by rw [hp0]; exact Vv_γ₀ h.natural.reduced.2.1
  obtain ⟨x, hxV, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hcrit
  have hx0 : x ∈ Vv V (p 0) := by rw [hV0]; exact hxV
  have hd1 : CosetGeom.dist (p 0) (p (m + 1)) ≤ m + 1 := by
    have := hp 0 (m + 1) (by omega) le_rfl
    omega
  have hd2 : CosetGeom.dist (p 0) (p m) ≤ m + 1 := by
    have := hp 0 m (by omega) (by omega)
    omega
  have hxa : x ∈ stab (p (m + 1)) := h.Vv_le_stab_A hb hv0 hd1 hx0
  have hxb : x ∈ stab (p m) := h.Vv_le_stab_A hb hv0 hd2 hx0
  have hnc : ¬ ∀ w ∈ Vv V (p (m + 1)), x * w * x⁻¹ = w := fun hall =>
    hxn (h.mem_ballStab_one_of_centralizes hev hxa hall)
  push Not at hnc
  obtain ⟨w, hw, hxw⟩ := hnc
  have hc1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e => hxw (mul_inv_eq_one.mp e)
  have hcm : x * w * x⁻¹ * w⁻¹ ∈ Zv z (p m) := h.commutator_mem_Zv hmm.symm hev ⟨hxa, hxb⟩ hw
  have hwa : w ∈ stab (p 0) := by
    refine h.Vv_le_stab_A hb hev ?_ hw
    rw [CosetGeom.dist_comm]
    exact hd1
  have hwb : w ∈ stab (p 1) := by
    refine h.Vv_le_stab_A hb hev ?_ hw
    rw [CosetGeom.dist_comm]
    have := hp 1 (m + 1) (by omega) le_rfl
    omega
  have hc1' : w * x * w⁻¹ * x⁻¹ ∈ Zv z (p 1) := h.commutator_mem_Zv h01 hv0 ⟨hwa, hwb⟩ hx0
  refine ⟨x * w * x⁻¹ * w⁻¹, hc1, ?_, hcm⟩
  have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (Zv z (p 1)).inv_mem hc1'

theorem coincidence_odd_I (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hp0 : p 0 = γ₀ (A ⊔ B) A B)
    (hcrit : ¬ V ≤ ballStab 1 (p (m + 1))) (hodd : vtype (p (m + 1)) = true)
    (hI : Vv V (p (m + 1)) ≤ ballStab 1 (p 1)) :
    ∃ c : D, c ≠ 1 ∧ c ∈ Zv z (p 1) ∧ c ∈ Vv V (p m) := by
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := hp.adj (i := m) (by omega)
  have hvm : vtype (p m) = false := vtype_eq_false_of_adj hmm.symm hodd
  have hV0 : Vv V (p 0) = V := by rw [hp0]; exact Vv_γ₀ h.natural.reduced.2.1
  obtain ⟨x, hxV, hxn⟩ := IsConcreteLE.not_le_iff_exists.1 hcrit
  have hx0 : x ∈ Vv V (p 0) := by rw [hV0]; exact hxV
  have hd1 : CosetGeom.dist (p 0) (p (m + 1)) ≤ m + 1 := by
    have := hp 0 (m + 1) (by omega) le_rfl
    omega
  have hd2 : CosetGeom.dist (p 0) (p m) ≤ m + 1 := by
    have := hp 0 m (by omega) (by omega)
    omega
  have hxa : x ∈ stab (p (m + 1)) := h.Vv_le_stab_A hb hv0 hd1 hx0
  have hxb : x ∈ stab (p m) := h.Vv_le_stab_A hb hv0 hd2 hx0
  have hnc : ¬ ∀ w ∈ Vv V (p (m + 1)), x * w * x⁻¹ * w⁻¹ ∈ Zv z (p (m + 1)) := fun hall =>
    hxn (h.mem_ballStab_one_of_commutator hodd hxa hall)
  push Not at hnc
  obtain ⟨w, hw, hxw⟩ := hnc
  have hc1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e => hxw (by rw [e]; exact (Zv z _).one_mem)
  have hcm : x * w * x⁻¹ * w⁻¹ ∈ Vv V (p m) := h.commutator_mem_Vv hU hmm hvm ⟨hxb, hxa⟩ hw
  have hwI : w ∈ ballStab 1 (p 1) := hI hw
  have hwb : w ∈ stab (p 1) := ballStab_le_stab 1 (p 1) hwI
  have hwa : w ∈ stab (p 0) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hwI
    rw [CosetGeom.dist_comm]
    have := hp 0 1 (by omega) (by omega)
    omega
  have hc1' : w * x * w⁻¹ * x⁻¹ ∈ Zv z (p 1) := h.commutator_mem_Zv h01 hv0 ⟨hwa, hwb⟩ hx0
  refine ⟨x * w * x⁻¹ * w⁻¹, hc1, ?_, hcm⟩
  have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact (Zv z (p 1)).inv_mem hc1'

theorem coincidence_odd_II (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 2 ≤ m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hv0 : vtype (p 0) = false)
    (hodd : vtype (p (m + 1)) = true) {γ : CosetGeom (A ⊔ B) A B}
    (hγ : (graph (A ⊔ B) A B).Adj (p (m + 1)) γ) (hnot : ¬ Vv V γ ≤ ballStab 1 (p 1)) :
    ∃ x ∈ Vv V (p 1), ∃ w ∈ Vv V γ, x * w * x⁻¹ * w⁻¹ ≠ 1 ∧
      x * w * x⁻¹ * w⁻¹ ∈ Vv V (p 2) ⊓ Vv V (p m) := by
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := hp.adj (i := 0) (by omega)
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := hp.adj (i := 1) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := hp.adj (i := m) (by omega)
  have hv1 : vtype (p 1) = true := vtype_eq_true_of_adj h01 hv0
  have hγt : vtype γ = false := vtype_eq_false_of_adj hγ hodd
  obtain ⟨w, hwγ, hwn⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hw : w ∈ Vv V (p (m + 1)) := Vv_le_Vv_of_adj hγ.symm hγt hwγ
  have hd1 : CosetGeom.dist (p 1) (p (m + 1)) ≤ m := by
    have := hp 1 (m + 1) (by omega) le_rfl
    omega
  have hd2 : CosetGeom.dist (p 1) (p m) ≤ m := by
    have := hp 1 m (by omega) (by omega)
    omega
  have hd3 : CosetGeom.dist (p (m + 1)) (p 1) ≤ m := by
    rw [CosetGeom.dist_comm]
    exact hd1
  have hd4 : CosetGeom.dist (p (m + 1)) (p 2) ≤ m := by
    rw [CosetGeom.dist_comm]
    have := hp 2 (m + 1) (by omega) le_rfl
    omega
  have hwb : w ∈ stab (p 1) := h.Vv_le_stab_B hb hodd hd3 hw
  have hnc : ¬ ∀ x ∈ Vv V (p 1), w * x * w⁻¹ * x⁻¹ ∈ Zv z (p 1) := fun hall =>
    hwn (h.mem_ballStab_one_of_commutator hv1 hwb hall)
  push Not at hnc
  obtain ⟨x, hx, hxw⟩ := hnc
  have e : w * x * w⁻¹ * x⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by group
  have hc1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e1 =>
    hxw (by rw [e, e1, inv_one]; exact (Zv z (p 1)).one_mem)
  exact ⟨x, hx, w, hwγ, hc1, h.commutator_mem_Vv_inf hU hb hv1 hodd h12 hmm.symm hd1 hd2 hd3 hd4
    hx hw⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
