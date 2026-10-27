module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VTwoLadder
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VDesc

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIIConfig V m p)

include c

theorem desc (h : GoldHyp3 A B z V) {j : ℕ} (hj : j + 2 ≤ m + 1) {H : Subgroup D}
    (hH : H ≤ ballStab 1 (p j))
    (hc : H ≤ Subgroup.centralizer (Zlab V z (p (j + 2)) : Set D)) :
    H ≤ ballStab 1 (p (j + 1)) := by
  have := h.le_ballStab_one_desc c.geo (i := j + 1) (by omega) (by omega) (H := H)
    (by simpa using hH) (by simpa using hc)
  exact this

theorem Vn_three_le (h : GoldHyp3 A B z V) (hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)) {u : D}
    (hu : u ∈ stab (p 1) ⊓ stab (p 2)) (huQ : u ∉ ballStab 1 (p 1))
    (hum : u ∈ ballStab 1 (p m)) : Vn V 3 (p 1) ≤ ballStab 1 (p m) := by
  have hm := c.eight_le
  have hb := c.critDist_eq
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have h01 : (graph (A ⊔ B) A B).Adj (p 1) (p 0) := c.adj_pred (by omega) le_rfl
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := c.adj (i := 1) (by omega)
  have h02 : p 0 ≠ p 2 := c.geo.ne (by omega) (by omega)
  have hum' : u ∈ stab (p m) := ballStab_le_stab 1 _ hum
  lift u to ↥(A ⊔ B) using stab_le _ hu.1 with g
  have hg1 : g • p 1 = p 1 := smul_eq_of_mem_stab hu.1
  have hg2 : g • p 2 = p 2 := smul_eq_of_mem_stab hu.2
  have hgm : g • p m = p m := smul_eq_of_mem_stab hum'
  have h13 : (graph (A ⊔ B) A B).Adj (p 1) (g • p 0) := by
    have := (smul_adj g).mpr h01
    rwa [hg1] at this
  have h03 : p 0 ≠ g • p 0 := fun e => huQ (h.mem_ballStab_one_of_fix_two hv1 h01 h12 h02 hu.1
    (mem_stab_of_smul_eq e.symm) hu.2)
  have h23 : p 2 ≠ g • p 0 := fun e => h02 (smul_left_cancel g (by rw [← e, hg2]))
  have hVn0 : Vn V 2 (g • p 0) ≤ ballStab 1 (p m) := by
    rw [← h.conjSub_Vn g 2 (p 0)]
    have := conjSub_mono (g : D) hBi
    rw [← ballStab_smul, hgm] at this
    exact this
  have hVn2 : Vn V 2 (p 2) ≤ ballStab 1 (p m) := by
    refine h.Vn_le_ballStab_one hb ?_
    rw [c.dist_eq (i := 2) (j := m) (by omega) (by omega)]
    omega
  have hpar : ∀ l : CosetGeom (A ⊔ B) A B, vtype l = false →
      CosetGeom.dist (p 1) l ≤ 3 → ∃ a, (graph (A ⊔ B) A B).Adj (p 1) a ∧
        CosetGeom.dist a l ≤ 2 := by
    intro l hl hd
    have hnev : ¬ Even (CosetGeom.dist (p 1) l) := fun he => by
      have := (vtype_eq_iff_even_dist rfl (p 1) l).mpr he
      rw [hv1, hl] at this
      exact absurd this (by decide)
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hnev
    rcases (by omega : CosetGeom.dist (p 1) l = 1 ∨ CosetGeom.dist (p 1) l = 3) with e | e
    · refine ⟨l, dist_eq_one_iff_adj.mp e, ?_⟩
      rw [CosetGeom.dist_self]
      omega
    · obtain ⟨β, hβ, hβd⟩ := exists_adj_dist_eq (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl
        (α := l) (δ := p 1) (d := 2) (by rw [CosetGeom.dist_comm, e])
      exact ⟨β, hβ, by rw [CosetGeom.dist_comm]; omega⟩
  refine Vn_le_iff.mpr fun l hl hd => ?_
  obtain ⟨a, ha, hal⟩ := hpar l hl hd
  refine (Vv_le_Vn hl hal).trans ?_
  rcases h.eq_or_eq_of_adj h01 h12 h13 ha h02 h03 h23 with e | e | e
  · rw [e]
    exact hBi
  · rw [e]
    exact hVn2
  · rw [e]
    exact hVn0

theorem Vv_le_Vn_three (h : GoldHyp3 A B z V) (hB3 : Vn V 3 (p 1) ≤ ballStab 1 (p m)) {u : D}
    (huV : u ∈ Vv V (p (m + 1))) (hu : u ∈ stab (p 1) ⊓ stab (p 2))
    (huQ : u ∉ ballStab 1 (p 1)) : Vv V (p m) ≤ Vn V 3 (p 1) := by
  have hm := c.eight_le
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have hv2 : vtype (p 2) = false := c.vtype_even (by omega) (by decide)
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := c.adj (i := 1) (by omega)
  obtain ⟨w, hw, hwn⟩ : ∃ w ∈ Vn V 3 (p 1), u * w * u⁻¹ * w⁻¹ ∉ Vv V (p 1) := by
    by_contra hcon
    push Not at hcon
    exact c.false_of_acts_trivially h (a := 1) (b' := 2) (c' := 3) (by omega) (by omega)
      (by omega) hu huQ (fun w hw => by rw [Vn_one_eq_Vv hv1]; exact hcon w hw)
  have hwQ : w ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ (hB3 hw),
      ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj).le (hB3 hw)⟩
  have hcw : u * w * u⁻¹ * w⁻¹ ∈ Vv V (p m) := by
    have := h.commutator_mem_Vv c.card hadj hmt hwQ huV
    have e : u * w * u⁻¹ * w⁻¹ = (w * u * w⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact (Vv V (p m)).inv_mem this
  have hcW : u * w * u⁻¹ * w⁻¹ ∈ Vn V 3 (p 1) :=
    (Vn V 3 (p 1)).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (h.stab_le_normalizer_Vn 3 (p 1) hu.1) w).mp hw) ((Vn V 3 (p 1)).inv_mem hw)
  obtain ⟨x, hx1, hx2, hxm, -⟩ := c.exists_c h
  obtain ⟨t, ht, hxt⟩ := h.exists_adj_mem_Zv hmt hxm hx1
  have htt : vtype t = true := vtype_eq_true_of_adj ht hmt
  have hx3 : x ∈ Vn V 3 (p 1) :=
    (Vv_le_Vn hv2 (by rw [c.dist_eq (by omega) (by omega)]; omega) : Vv V (p 2) ≤ Vn V 3 (p 1))
      hx2
  have hx4 : x ∈ Vv V (p 1) := Vv_le_Vv_of_adj h12.symm hv2 hx2
  have hZW : Zv z t ≤ Vn V 3 (p 1) := le_of_card_two_of_mem (h.card_Zv htt) hxt hx3 hx1
  have hZ1 : Zv z t ≤ Vv V (p 1) := le_of_card_two_of_mem (h.card_Zv htt) hxt hx4 hx1
  exact le_of_card_four (h.card_Vv_A hmt) (h.card_Zv htt) (h.Zv_le_Vv ht hmt) hZW hcw hcW
    (fun hz => hwn (hZ1 hz))

theorem false_of_Bi (h : GoldHyp3 A B z V) (hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)) : False := by
  have hb := c.critDist_eq
  have hm := c.eight_le
  obtain ⟨k, hk⟩ := c.even
  obtain ⟨u, huV, hu2, hu, huQ⟩ := c.exists_u h
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  have hum : u ∈ ballStab 1 (p m) := by
    refine h.VvB_le_ballStab_one_of_dist hb hbt ?_ huV
    rw [CosetGeom.dist_comm, c.dist_eq (i := m) (j := m + 1) (by omega) le_rfl]
    omega
  have hB3 : Vn V 3 (p 1) ≤ ballStab 1 (p m) := c.Vn_three_le h hBi hu huQ hum
  have hVm : Vv V (p m) ≤ Vn V 3 (p 1) := c.Vv_le_Vn_three h hB3 huV hu huQ
  have hHW : Vn V 5 (p 1) ≤ Subgroup.centralizer (Vn V 3 (p 1) : Set D) :=
    h.Vn_le_centralizer_Vn hb (n := 5) (n' := 3) (by rw [CosetGeom.dist_self]; omega)
  have cent : ∀ Y : Subgroup D, Y ≤ Vn V 3 (p 1) →
      Vn V 5 (p 1) ≤ Subgroup.centralizer (Y : Set D) := fun Y hY =>
    hHW.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hY))
  have cent' : ∀ Y : Subgroup D, Y ≤ Vn V 3 (p 1) →
      Y ≤ Subgroup.centralizer (Vn V 5 (p 1) : Set D) := fun Y hY =>
    Subgroup.le_centralizer_iff.mp (cent Y hY)
  have hH0 : Vn V 5 (p 1) ≤ ballStab 1 (p (m - 4)) := by
    refine h.Vn_le_ballStab_one hb ?_
    rw [c.dist_eq (i := 1) (j := m - 4) (by omega) (by omega)]
    omega
  have hm1t : vtype (p (m - 1)) = true := c.vtype_odd (by omega) ⟨k - 1, by omega⟩
  have hm3t : vtype (p (m - 3)) = true := c.vtype_odd (by omega) ⟨k - 2, by omega⟩
  have hm2t : vtype (p (m - 2)) = false := c.vtype_even (by omega) ⟨k - 1, by omega⟩
  have hZ1 : Zv z (p (m - 1)) ≤ Vn V 3 (p 1) :=
    (h.Zv_le_Vv (c.adj_pred (i := m) (by omega) (by omega)) hmt).trans hVm
  have hZ2 : Zv z (p (m + 1)) ≤ Vn V 3 (p 1) := (h.Zv_le_Vv hadj hmt).trans hVm
  have hne : p (m - 3) ≠ p (m - 1) := c.geo.ne (by omega) (by omega)
  have hc3 : Zv z (p (m - 3)) ≤ Subgroup.centralizer (Vn V 5 (p 1) : Set D) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgs : g ∈ stab (p (m - 3)) := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr (c.adj' (i := m - 4) (j := m - 3) (by omega) (by omega))).le
      (hH0 hg)
    exact mul_inv_eq_iff_eq_mul.mp (h.stab_centralizes_Zv hm3t hgs hx)
  have hV3 : Vv V (p (m - 2)) ≤ Subgroup.centralizer (Vn V 5 (p 1) : Set D) :=
    h.Vv_le_centralizer_of_two_labels hm2t
      (c.adj' (i := m - 3) (j := m - 2) (by omega) (by omega)).symm
      (c.adj' (i := m - 2) (j := m - 1) (by omega) (by omega)) hne hc3 (cent' _ hZ1)
  have hH1 : Vn V 5 (p 1) ≤ ballStab 1 (p (m - 3)) := by
    have := c.desc h (j := m - 4) (by omega) hH0 (by
      rw [show m - 4 + 2 = m - 2 by omega, Zlab_of_vtype_false hm2t]
      exact Subgroup.le_centralizer_iff.mp hV3)
    rwa [show m - 4 + 1 = m - 3 by omega] at this
  have hH2 : Vn V 5 (p 1) ≤ ballStab 1 (p (m - 2)) := by
    have := c.desc h (j := m - 3) (by omega) hH1 (by
      rw [show m - 3 + 2 = m - 1 by omega, Zlab_of_vtype_true hm1t]
      exact cent _ hZ1)
    rwa [show m - 3 + 1 = m - 2 by omega] at this
  have hH3 : Vn V 5 (p 1) ≤ ballStab 1 (p (m - 1)) := by
    have := c.desc h (j := m - 2) (by omega) hH2 (by
      rw [show m - 2 + 2 = m by omega, Zlab_of_vtype_false hmt]
      exact cent _ hVm)
    rwa [show m - 2 + 1 = m - 1 by omega] at this
  have hH4 : Vn V 5 (p 1) ≤ ballStab 1 (p m) := by
    have := c.desc h (j := m - 1) (by omega) hH3 (by
      rw [show m - 1 + 2 = m + 1 by omega, Zlab_of_vtype_true hbt]
      exact cent _ hZ2)
    rwa [show m - 1 + 1 = m by omega] at this
  refine c.false_of_acts_trivially h (a := 3) (b' := 4) (c' := 5) (by omega) (by omega)
    (by omega) hu huQ fun w hw => ?_
  have hwQ : w ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ (hH4 hw),
      ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj).le (hH4 hw)⟩
  have := h.commutator_mem_Vv c.card hadj hmt hwQ huV
  have e : u * w * u⁻¹ * w⁻¹ = (w * u * w⁻¹ * u⁻¹)⁻¹ := by group
  rw [e]
  exact (Vn V 3 (p 1)).inv_mem (hVm this)

end TypeIIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
