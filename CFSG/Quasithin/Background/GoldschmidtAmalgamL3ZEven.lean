module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VDesc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFrat

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure EvenCritG (V : Subgroup D) (m : ℕ) (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  crit : critDist (A ⊔ B) A B V = m + 1
  seven_le : 7 ≤ m
  odd : Odd m
  geo : IsGeo p (m + 1)
  start : p 0 = γ₀ (A ⊔ B) A B
  not_le : ¬ V ≤ ballStab 1 (p (m + 1))

namespace EvenCritG

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B}

theorem vt_false (e : EvenCritG V m p) {i : ℕ} (hi : i ≤ m + 1) (he : Even i) :
    vtype (p i) = false :=
  e.geo.vtype_false_of_even rfl e.start hi he

theorem vt_true (e : EvenCritG V m p) {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) :
    vtype (p i) = true :=
  e.geo.vtype_true_of_odd rfl e.start hi ho

theorem adj (e : EvenCritG V m p) {i j : ℕ} (hj : j = i + 1) (hi : i < m + 1) :
    (graph (A ⊔ B) A B).Adj (p i) (p j) := by
  subst hj
  exact e.geo.adj hi

theorem dist_eq (e : EvenCritG V m p) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1) :
    CosetGeom.dist (p i) (p j) = j - i := e.geo i j hij hj

variable [Finite D] (h : GoldHyp3 A B z V) (e : EvenCritG V m p)

include h e

theorem exists_c : ∃ c : D, c ≠ 1 ∧ c ∈ Zv z (p 1) ∧ c ∈ Zv z (p m) :=
  h.coincidence_even e.crit e.geo e.start e.not_le (e.vt_false le_rfl e.odd.add_one)

theorem Zv_eq : Zv z (p m) = Zv z (p 1) := by
  obtain ⟨c, hc1, hc1', hcm⟩ := exists_c h e
  have h1t : vtype (p 1) = true := e.vt_true (by have := e.seven_le; omega) odd_one
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  exact le_antisymm (le_of_card_two_of_mem (h.card_Zv hmt) hcm hc1' hc1)
    (le_of_card_two_of_mem (h.card_Zv h1t) hc1' hcm hc1)

omit [Finite D] in
theorem Zv_le_W : Zv z (p 1) ≤ Vn V 2 (p 0) := by
  have h0 : vtype (p 0) = false := e.vt_false (by have := e.seven_le; omega) ⟨0, rfl⟩
  exact (h.Zv_le_Vv (e.adj (i := 0) (j := 1) rfl (by have := e.seven_le; omega)) h0).trans
    (Vv_le_Vn h0 (by rw [CosetGeom.dist_self]; omega))

theorem W_abelian : Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn e.crit (by rw [CosetGeom.dist_self]; have := e.seven_le; omega)

theorem good : Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  have hm := e.seven_le
  refine h.le_ballStab_one_desc e.geo (i := m - 1) (by omega) (by omega) ?_ ?_
  · refine h.Vn_le_ballStab_one e.crit ?_
    have := e.dist_eq (i := 0) (j := m - 1 - 1) (Nat.zero_le _) (by omega)
    omega
  · rw [show m - 1 + 1 = m by omega, Zlab_of_vtype_true (e.vt_true (by omega) e.odd),
      Zv_eq h e]
    exact (W_abelian h e).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (Zv_le_W h e)))

theorem exists_far : ∃ v ∈ Vv V (p (m + 1)), v ∉ ballStab 1 (p 0) := by
  have hm := e.seven_le
  have hv0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have hV0 : Vv V (p 0) = V := by
    rw [e.start]
    exact Vv_γ₀ h.natural.reduced.2.1
  obtain ⟨x, hxV, hxn⟩ := IsConcreteLE.not_le_iff_exists.mp e.not_le
  have hx0 : x ∈ Vv V (p 0) := by rw [hV0]; exact hxV
  have hxa : x ∈ stab (p (m + 1)) := by
    refine h.Vv_le_stab_A e.crit hv0 ?_ hx0
    have := e.dist_eq (i := 0) (j := m + 1) (Nat.zero_le _) le_rfl
    omega
  have hnc : ¬ ∀ w ∈ Vv V (p (m + 1)), x * w * x⁻¹ = w := fun hall =>
    hxn (h.mem_ballStab_one_of_centralizes hev hxa hall)
  push Not at hnc
  obtain ⟨w, hw, hxw⟩ := hnc
  refine ⟨w, hw, fun hwQ => hxw ?_⟩
  have h1 := h.ballStab_one_le_centralizer_Vv hv0 hwQ hx0
  exact mul_inv_eq_iff_eq_mul.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem Vv_far_le_stab : Vv V (p (m + 1)) ≤ stab (p 0) ⊓ stab (p 1) := by
  have hm := e.seven_le
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have h1 : Vv V (p (m + 1)) ≤ ballStab 1 (p 1) := by
    refine h.Vv_le_ballStab_one_of_dist e.crit hev ?_
    have := e.dist_eq (i := 1) (j := m + 1) (by omega) le_rfl
    rw [CosetGeom.dist_comm]
    omega
  refine le_inf (h1.trans (ballStab_le_stab_of_dist_le (n := 1) ?_))
    (h1.trans (ballStab_le_stab 1 _))
  have := e.dist_eq (i := 0) (j := 1) (by omega) (by omega)
  rw [CosetGeom.dist_comm]
  omega

theorem not_W_le_Q {n : ℕ} (hU : Nat.card (conjClosure V B) = n) (hn : n ≠ 1) :
    ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m) := by
  intro hW
  have hm := e.seven_le
  have hv0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have h1t : vtype (p 1) = true := e.vt_true (by omega) odd_one
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := e.adj (i := 0) (j := 1) rfl (by omega)
  obtain ⟨v, hv, hvn⟩ := exists_far h e
  have hvT := Vv_far_le_stab h e hv
  have hmm : (graph (A ⊔ B) A B).Adj (p (m + 1)) (p m) :=
    (e.adj (i := m) (j := m + 1) rfl (by omega)).symm
  have hYZ : Vv V (p 0) ≤ Vv V (p 1) := Vv_le_Vv_of_adj h01 hv0
  have hZY : Vv V (p 1) ≤ Vn V 2 (p 0) := by
    refine (Vv_B_le_iff h1t).mpr fun u hu => ?_
    have hut : vtype u = false := vtype_eq_false_of_adj hu h1t
    refine Vv_le_Vn hut ?_
    have h1 := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 0) (p 1) u
    have h2 : CosetGeom.dist (p 0) (p 1) = 1 := CosetGeom.dist_eq_one_iff_adj.mpr h01
    have h3 : CosetGeom.dist (p 1) u = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hu
    omega
  have hZT : Vv V (p 1) ≤ stab (p 0) ⊓ stab (p 1) := by
    have hb1 : Vv V (p 1) ≤ ballStab 1 (p 1) := by
      refine h.VvB_le_ballStab_one_of_dist e.crit h1t ?_
      rw [CosetGeom.dist_self]
      omega
    refine le_inf (hb1.trans (ballStab_le_stab_of_dist_le (n := 1) ?_))
      (hb1.trans (ballStab_le_stab 1 _))
    rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr h01]
  have hcomm : ∀ w ∈ Vn V 2 (p 0), v * w * v⁻¹ * w⁻¹ ∈ Vv V (p 0) := by
    intro w hw
    have hwq := hW hw
    have hwa : w ∈ stab (p (m + 1)) := ballStab_le_stab_of_dist_le (n := 1)
      (by rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hmm]) hwq
    have hwb : w ∈ stab (p m) := ballStab_le_stab 1 _ hwq
    have hc := h.commutator_mem_Zv hmm hev ⟨hwa, hwb⟩ hv
    have hinv : v * w * v⁻¹ * w⁻¹ = (w * v * w⁻¹ * v⁻¹)⁻¹ := by group
    rw [hinv]
    refine Vv V (p 0) |>.inv_mem ?_
    have : w * v * w⁻¹ * v⁻¹ ∈ Zv z (p 1) := by rw [← Zv_eq h e]; exact hc
    exact h.Zv_le_Vv h01 hv0 this
  have hbot := h.eq_bot_of_acts_trivially h01 hYZ hZY hZT
    (stab_le_normalizer_Vv h.natural.reduced.2.1 (p 0)) (h.stab_le_normalizer_Vn 2 (p 0))
    (stab_le_normalizer_Vv h.natural.reduced.2.1 (p 1)) hvT hvn hcomm
  have hc := h.card_Vv_B_of_card hU h1t
  rw [hbot] at hc
  simp at hc
  omega

theorem false_of_even (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u) : False := by
  have hm := e.seven_le
  have hv0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := e.adj (i := 0) (j := 1) rfl (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p (m + 1)) (p m) :=
    (e.adj (i := m) (j := m + 1) rfl (by omega)).symm
  have hadjm : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := e.adj (by omega) (by omega)
  have hbad := not_W_le_Q h e hU (by norm_num)
  obtain ⟨g₀, hg₀W, hg₀n⟩ := IsConcreteLE.not_le_iff_exists.mp hbad
  obtain ⟨v, hv, hvn⟩ := exists_far h e
  have hvT := Vv_far_le_stab h e hv
  have hgood := good h e
  have hdm : CosetGeom.dist (p (m - 1)) (p m) ≤ 1 := (CosetGeom.dist_eq_one_iff_adj.mpr hadjm).le
  have hstab : ∀ w ∈ Vn V 2 (p 0), w ∈ stab (p m) ⊓ stab (p (m - 1)) := fun w hw =>
    ⟨ballStab_le_stab_of_dist_le (n := 1) hdm (hgood hw), ballStab_le_stab 1 _ (hgood hw)⟩
  have hWv : ∀ w ∈ Vn V 2 (p 0), v * w * v⁻¹ ∈ Vn V 2 (p 0) := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (h.stab_le_normalizer_Vn 2 (p 0) (hvT.1)) w).mp hw
  have hab := W_abelian h e
  have hleft : ∀ w ∈ Vn V 2 (p 0), w ∈ ballStab 1 (p m) →
      w * v * w⁻¹ * v⁻¹ ∈ Vv V (p 0) := by
    intro w _ hwq
    have hwa : w ∈ stab (p (m + 1)) := ballStab_le_stab_of_dist_le (n := 1)
      (by rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hmm]) hwq
    have hwb : w ∈ stab (p m) := ballStab_le_stab 1 _ hwq
    have hc := h.commutator_mem_Zv hmm hev ⟨hwa, hwb⟩ hv
    rw [Zv_eq h e] at hc
    exact h.Zv_le_Vv h01 hv0 hc
  refine h.false_of_comm_mem_cosets hU hI1 hv0 h01 hab hvT hvn
    (f := g₀ * v * g₀⁻¹ * v⁻¹) ?_
  intro w hw
  by_cases hwq : w ∈ ballStab 1 (p m)
  · exact Or.inl (hleft w hw hwq)
  · right
    have hq : w * g₀⁻¹ ∈ ballStab 1 (p m) :=
      h.mul_inv_mem_ballStab_one hadjm.symm (hstab w hw) (hstab g₀ hg₀W) hwq hg₀n
    have hqW : w * g₀⁻¹ ∈ Vn V 2 (p 0) := (Vn V 2 (p 0)).mul_mem hw ((Vn V 2 (p 0)).inv_mem hg₀W)
    have hfW : g₀ * v * g₀⁻¹ * v⁻¹ ∈ Vn V 2 (p 0) := by
      have := (Vn V 2 (p 0)).mul_mem hg₀W (hWv g₀⁻¹ ((Vn V 2 (p 0)).inv_mem hg₀W))
      have e1 : g₀ * v * g₀⁻¹ * v⁻¹ = g₀ * (v * g₀⁻¹ * v⁻¹) := by group
      rw [e1]
      exact this
    have hcomm : (w * g₀⁻¹) * (g₀ * v * g₀⁻¹ * v⁻¹) = (g₀ * v * g₀⁻¹ * v⁻¹) * (w * g₀⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hab hfW) _ hqW)
    have hd := hleft _ hqW hq
    have e3 : w * v * w⁻¹ * v⁻¹ =
        (w * g₀⁻¹) * (g₀ * v * g₀⁻¹ * v⁻¹) * (v * (w * g₀⁻¹)⁻¹ * v⁻¹) := by group
    have e2 : (g₀ * v * g₀⁻¹ * v⁻¹)⁻¹ * (w * v * w⁻¹ * v⁻¹) =
        (w * g₀⁻¹) * v * (w * g₀⁻¹)⁻¹ * v⁻¹ := by
      calc (g₀ * v * g₀⁻¹ * v⁻¹)⁻¹ * (w * v * w⁻¹ * v⁻¹)
          = (g₀ * v * g₀⁻¹ * v⁻¹)⁻¹ * ((w * g₀⁻¹) * (g₀ * v * g₀⁻¹ * v⁻¹) *
              (v * (w * g₀⁻¹)⁻¹ * v⁻¹)) := by rw [← e3]
        _ = (g₀ * v * g₀⁻¹ * v⁻¹)⁻¹ * ((g₀ * v * g₀⁻¹ * v⁻¹) * (w * g₀⁻¹) *
              (v * (w * g₀⁻¹)⁻¹ * v⁻¹)) := by rw [hcomm]
        _ = (w * g₀⁻¹) * v * (w * g₀⁻¹)⁻¹ * v⁻¹ := by group
    rw [e2]
    exact hd

end EvenCritG

end GoldAmL3

end F6

end CFSG.Quasithin
