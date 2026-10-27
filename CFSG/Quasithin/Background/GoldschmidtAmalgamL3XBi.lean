module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XLadder

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace TypeIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIConfig V m p)

include c

theorem Vv_le_of_Bi (h : GoldHyp3 A B z V) (hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)) {u : D}
    (huV : u ∈ Vv V (p (m + 1))) (huT : u ∈ stab (p 0) ⊓ stab (p 1))
    (huQ : u ∉ ballStab 1 (p 0)) : Vv V (p m) ≤ Vn V 2 (p 0) := by
  have hm6 := c.six_le
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  obtain ⟨w, hw, hwn⟩ : ∃ w ∈ Vn V 2 (p 0), u * w * u⁻¹ * w⁻¹ ∉ Vv V (p 0) := by
    by_contra hcon
    push Not at hcon
    exact c.false_of_acts_trivially h (a := 0) (b' := 1) (c' := 2) (by omega) (by omega)
      (by omega) huT huQ (fun w hw => by rw [c.Vn_zero_eq]; exact hcon w hw)
  have hwQ : w ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ (hBi hw),
      ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj).le (hBi hw)⟩
  have hcw : u * w * u⁻¹ * w⁻¹ ∈ Vv V (p m) := by
    have := h.commutator_mem_Vv c.card hadj hmt hwQ huV
    have e : u * w * u⁻¹ * w⁻¹ = (w * u * w⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact (Vv V (p m)).inv_mem this
  have hcW : u * w * u⁻¹ * w⁻¹ ∈ Vn V 2 (p 0) :=
    (Vn V 2 (p 0)).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (h.stab_le_normalizer_Vn 2 (p 0) huT.1) w).mp hw) ((Vn V 2 (p 0)).inv_mem hw)
  have hZ1 : Zv z (p 1) ≤ Vv V (p 0) := h.Zv_le_Vv (c.adj (Nat.zero_le _)) c.vtype_zero
  exact le_of_card_four (h.card_Vv_A hmt) (h.card_Zv hv1) (c.Zv_one_le h)
    (hZ1.trans (Vv_le_Vn c.vtype_zero (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)))
    hcw hcW (fun hz => hwn (hZ1 hz))

theorem false_of_Bi (h : GoldHyp3 A B z V) (hBi : Vn V 2 (p 0) ≤ ballStab 1 (p m)) : False := by
  have hb := c.critDist_eq
  have hm6 := c.six_le
  obtain ⟨k, hk⟩ := c.even
  obtain ⟨u, huV, huT, huQ⟩ := c.exists_u h
  have hmt : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hadj : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  have hVm := c.Vv_le_of_Bi h hBi huV huT huQ
  have hHW : Vn V 4 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
    h.Vn_le_centralizer_Vn hb (n := 4) (n' := 2) (by rw [CosetGeom.dist_self]; omega)
  have hcent : ∀ S : Subgroup D, S ≤ Vn V 2 (p 0) →
      S ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) := fun S hS x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp (hHW hg)) x (hS hx)).symm
  have hH0 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 4)) :=
    h.Vn_le_ballStab_one hb (by rw [c.dist_zero (by omega)]; omega)
  have hZ1 : Zv z (p (m - 1)) ≤ Vn V 2 (p 0) :=
    (h.Zv_le_Vv (c.adj_pred (by omega) (by omega) : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)))
      hmt).trans hVm
  have hZ2 : Zv z (p (m + 1)) ≤ Vn V 2 (p 0) := (h.Zv_le_Vv hadj hmt).trans hVm
  have hne : p (m - 3) ≠ p (m - 1) := c.geo.ne (by omega) (by omega)
  have hc3 : Zv z (p (m - 3)) ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgs : g ∈ stab (p (m - 3)) := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr (c.adj' (i := m - 4) (j := m - 3) (by omega) (by omega))).le
      (hH0 hg)
    exact mul_inv_eq_iff_eq_mul.mp (h.stab_centralizes_Zv
      (c.vtype_odd (by omega) (⟨k - 2, by omega⟩ : Odd (m - 3))) hgs hx)
  have hV3 : Vv V (p (m - 2)) ≤ Subgroup.centralizer (Vn V 4 (p 0) : Set D) :=
    h.Vv_le_centralizer_of_two_labels
      (c.vtype_even (by omega) (⟨k - 1, by omega⟩ : Even (m - 2)))
      (c.adj' (i := m - 3) (j := m - 2) (by omega) (by omega)).symm
      (c.adj' (i := m - 2) (j := m - 1) (by omega) (by omega)) hne hc3 (hcent _ hZ1)
  have hH1 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 3)) := by
    have := c.desc h (j := m - 4) (by omega) hH0 (by
      rw [show m - 4 + 2 = m - 2 by omega, c.Zlab_even (by omega) ⟨k - 1, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp hV3)
    rwa [show m - 4 + 1 = m - 3 by omega] at this
  have hH2 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 2)) := by
    have := c.desc h (j := m - 3) (by omega) hH1 (by
      rw [show m - 3 + 2 = m - 1 by omega, c.Zlab_odd (by omega) ⟨k - 1, by omega⟩]
      exact Subgroup.le_centralizer_iff.mp (hcent _ hZ1))
    rwa [show m - 3 + 1 = m - 2 by omega] at this
  have hH3 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 1)) := by
    have := c.desc h (j := m - 2) (by omega) hH2 (by
      rw [show m - 2 + 2 = m by omega, c.Zlab_even (by omega) c.even]
      exact Subgroup.le_centralizer_iff.mp (hcent _ hVm))
    rwa [show m - 2 + 1 = m - 1 by omega] at this
  have hH4 : Vn V 4 (p 0) ≤ ballStab 1 (p m) := by
    have := c.desc h (j := m - 1) (by omega) hH3 (by
      rw [show m - 1 + 2 = m + 1 by omega, c.Zlab_odd le_rfl c.even.add_one]
      exact Subgroup.le_centralizer_iff.mp (hcent _ hZ2))
    rwa [show m - 1 + 1 = m by omega] at this
  refine c.false_of_acts_trivially h (a := 2) (b' := 3) (c' := 4) (by omega) (by omega)
    (by omega) huT huQ fun w hw => ?_
  have hwQ : w ∈ stab (p m) ⊓ stab (p (m + 1)) :=
    ⟨ballStab_le_stab 1 _ (hH4 hw),
      ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr hadj).le (hH4 hw)⟩
  have := h.commutator_mem_Vv c.card hadj hmt hwQ huV
  have e : u * w * u⁻¹ * w⁻¹ = (w * u * w⁻¹ * u⁻¹)⁻¹ := by group
  rw [e]
  exact (Vn V 2 (p 0)).inv_mem (hVm this)

end TypeIConfig

end GoldAmL3

end F6

end CFSG.Quasithin
