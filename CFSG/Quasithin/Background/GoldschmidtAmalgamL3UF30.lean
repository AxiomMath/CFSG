module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UCent
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RZCrit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UFix

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

theorem exists_ne_one_mem_Vv_inf {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 2 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hv0 : vtype (p 0) = false)
    (hcrit : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1))) :
    ∃ c : D, c ≠ 1 ∧ c ∈ Vv V (p 2) ∧ c ∈ Vv V (p m) := by
  have hmt : vtype (p m) = false := hp.vtype_false_of_even_start rfl hv0 (by omega) hev
  have hbt : vtype (p (m + 1)) = true := hp.vtype_true_of_odd_start rfl hv0 le_rfl hev.add_one
  have h2t : vtype (p 2) = false := hp.vtype_false_of_even_start rfl hv0 (by omega) (by decide)
  obtain ⟨x₀, hx₀V, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 hcrit
  have hx₀m : x₀ ∈ stab (p m) :=
    h.Vv_le_stab_A hb hv0 (by rw [hp 0 m (Nat.zero_le _) (by omega)]; omega) hx₀V
  have hx₀b : x₀ ∈ stab (p (m + 1)) :=
    h.Vv_le_stab_A hb hv0 (by rw [hp 0 (m + 1) (Nat.zero_le _) le_rfl]; omega) hx₀V
  obtain ⟨w, hwV, hw⟩ : ∃ w ∈ Vv V (p (m + 1)),
      x₀ * w * x₀⁻¹ * w⁻¹ ∉ Zv z (p (m + 1)) := by
    by_contra hcon
    push Not at hcon
    exact hx₀Q (h.mem_ballStab_one_of_commutator hbt hx₀b hcon)
  have hw1 : w ∈ stab (p 1) :=
    h.Vv_le_stab_B hb hbt (by rw [CosetGeom.dist_comm, hp 1 (m + 1) (by omega) le_rfl]; omega) hwV
  have hw2 : w ∈ stab (p 2) :=
    h.Vv_le_stab_B hb hbt (by rw [CosetGeom.dist_comm, hp 2 (m + 1) (by omega) le_rfl]; omega) hwV
  have hx₁ : x₀ ∈ Vv V (p 1) := Vv_le_Vv_of_adj (hp.adj (i := 0) (by omega)) hv0 hx₀V
  refine ⟨x₀ * w * x₀⁻¹ * w⁻¹, fun e => hw (by rw [e]; exact one_mem _), ?_, ?_⟩
  · have := h.commutator_mem_Vv hU (hp.adj (i := 1) (by omega)).symm h2t ⟨hw2, hw1⟩ hx₁
    have e : x₀ * w * x₀⁻¹ * w⁻¹ = (w * x₀ * w⁻¹ * x₀⁻¹)⁻¹ := by group
    rw [e]
    exact (Vv V (p 2)).inv_mem this
  · exact h.commutator_mem_Vv hU (hp.adj (i := m) (by omega)) hmt ⟨hx₀m, hx₀b⟩ hwV

theorem exists_swap {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 2 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hv0 : vtype (p 0) = false)
    {v : CosetGeom (A ⊔ B) A B} (hv : (graph (A ⊔ B) A B).Adj (p 0) v)
    (hbad : ¬ Vv V v ≤ ballStab 1 (p (m - 1))) :
    ∃ g ∈ Vv V v, ∃ x' : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj (p (m - 1)) x' ∧
      x' ≠ p m ∧ ∀ c ∈ Vv V (p m), g * c * g⁻¹ ∈ Vv V x' := by
  have hvt : vtype v = true := vtype_eq_true_of_adj hv hv0
  have hut : vtype (p (m - 1)) = true := hp.vtype_true_of_odd_start rfl hv0 (by omega) (by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩)
  have a1 : (graph (A ⊔ B) A B).Adj (p (m - 2)) (p (m - 1)) := by
    have := hp.adj (i := m - 2) (by omega)
    rwa [show m - 2 + 1 = m - 1 by omega] at this
  have a2 : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := by
    have := hp.adj (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have hd1 : Vv V v ≤ ballStab 1 (p (m - 2)) := by
    refine h.VvB_le_ballStab_one_of_dist hb hvt ?_
    have h1 : CosetGeom.dist v (p 0) = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr hv
    have h2 := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) v (p 0) (p (m - 2))
    have h3 := hp 0 (m - 2) (Nat.zero_le _) (by omega)
    omega
  obtain ⟨g, hgV, hgQ⟩ := IsConcreteLE.not_le_iff_exists.1 hbad
  have hg2 : g ∈ ballStab 1 (p (m - 2)) := hd1 hgV
  have hgu : g ∈ stab (p (m - 1)) := ballStab_le_stab_of_dist_le
    (by rw [hp (m - 2) (m - 1) (by omega) (by omega)]; omega) hg2
  have hne : p (m - 2) ≠ p m := hp.ne (i := m - 2) (j := m) (by omega) (by omega)
  have hgm : g ∉ stab (p m) := fun hgm => hgQ
    (h.mem_ballStab_one_of_fix_two hut a1.symm a2 hne hgu (ballStab_le_stab _ _ hg2) hgm)
  have hgG : g ∈ A ⊔ B := stab_le _ hgu
  lift g to ↥(A ⊔ B) using hgG with g'
  have hg'u : g' • p (m - 1) = p (m - 1) := smul_eq_of_mem_stab hgu
  refine ⟨(g' : D), hgV, g' • p m, ?_, fun e => hgm (mem_stab_of_smul_eq e), fun c hc => ?_⟩
  · have := (smul_adj g').mpr a2
    rwa [hg'u] at this
  · rw [Vv_smul h.natural.reduced.2.1 g' (p m)]
    exact mul_mem_conjSub hc

theorem Zv_le_Vv_of_bad_neighbour {m : ℕ} (hU : Nat.card (conjClosure V B) = 8)
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 4 ≤ m) (hev : Even m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hv0 : vtype (p 0) = false)
    (hcrit : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)))
    {v : CosetGeom (A ⊔ B) A B} (hv : (graph (A ⊔ B) A B).Adj (p 0) v)
    (hbad : ¬ Vv V v ≤ ballStab 1 (p (m - 1))) : Zv z (p (m - 1)) ≤ Vv V (p 2) := by
  obtain ⟨c, hc1, hc2, hcm⟩ := h.exists_ne_one_mem_Vv_inf hU hb (by omega) hev hp hv0 hcrit
  obtain ⟨g, hgV, x', hx', hne, hswap⟩ := h.exists_swap hb (by omega) hev hp hv0 hv hbad
  have hvt : vtype v = true := vtype_eq_true_of_adj hv hv0
  have h2t : vtype (p 2) = false := hp.vtype_false_of_even_start rfl hv0 (by omega) (by decide)
  have hut : vtype (p (m - 1)) = true := hp.vtype_true_of_odd_start rfl hv0 (by omega) (by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩)
  have a2 : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := by
    have := hp.adj (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have hcomm : g ∈ Subgroup.centralizer (Vv V (p 2) : Set D) := by
    refine ((Vv_B_le_iff hvt).mpr fun μ hμ => ?_) hgV
    refine h.Vv_le_centralizer_of_dist hb (vtype_eq_false_of_adj hμ hvt) h2t ?_
    have h1 : CosetGeom.dist μ v = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr hμ
    have h1' : CosetGeom.dist v (p 0) = 1 := by
      rw [CosetGeom.dist_comm]
      exact dist_eq_one_iff_adj.mpr hv
    have ha := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) μ v (p 2)
    have hb' := CosetGeom.dist_triangle (rfl : A ⊔ B = A ⊔ B) v (p 0) (p 2)
    have h02 := hp 0 2 (by omega) (by omega)
    omega
  have hgc : g * c * g⁻¹ = c := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hcomm c hc2).symm
  have hcx : c ∈ Vv V x' := by
    have := hswap c hcm
    rwa [hgc] at this
  exact le_of_card_two_of_mem (h.card_Zv hut)
    (h.mem_Zv_of_mem_Vv_of_mem_Vv hut a2 hx' hne.symm hcm hcx) hc2 hc1

theorem mem_Zv_of_mem_Vv_of_mem_ballStab {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1)
    {q : ℕ → CosetGeom (A ⊔ B) A B} (hq : IsGeo q (m + 1)) (hq0 : vtype (q 0) = false)
    (hcrit : ¬ Vv V (q 0) ≤ ballStab 1 (q (m + 1))) {c : D} (hc : c ∈ Vv V (q 0))
    (hcQ : c ∈ ballStab 1 (q (m + 1))) : c ∈ Zv z (q 1) := by
  have h1t : vtype (q 1) = true := hq.vtype_true_of_odd_start rfl hq0 (by omega) (by decide)
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup D, K = Vv V (q 0) ⊓ ballStab 1 (q (m + 1)) := ⟨_, rfl⟩
  have hK : Zv z (q 1) ≤ K := by
    rw [hKdef]
    exact le_inf (h.Zv_le_Vv (hq.adj (i := 0) (by omega)) hq0)
      (h.Zv_le_ballStab_one_of_dist_le hb h1t
        (by rw [hq 1 (m + 1) (by omega) le_rfl]; omega))
  have hle : K ≤ Vv V (q 0) := by
    rw [hKdef]
    exact inf_le_left
  have hleQ : K ≤ ballStab 1 (q (m + 1)) := by
    rw [hKdef]
    exact inf_le_right
  have h4 : Nat.card (Vv V (q 0)) = 4 := h.card_Vv_A hq0
  have h2 : Nat.card (Zv z (q 1)) = 2 := h.card_Zv h1t
  have hd1 : 2 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le hK
    rwa [h2] at this
  have hd2 : Nat.card K ∣ 4 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h4] at this
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hle4 := Nat.le_of_dvd (by norm_num) hd2
  have hne4 : Nat.card K ≠ 4 := fun e => hcrit (by
    have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [← heq]
    exact hleQ)
  have heq : Zv z (q 1) = K := Subgroup.eq_of_le_of_card_ge hK (by omega)
  rw [heq, hKdef]
  exact ⟨hc, hcQ⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
