module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VCrit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3XFrat
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VDesc

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure EvenCrit (V : Subgroup D) (m : ℕ) (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  card_eq : Nat.card (conjClosure V B) = 8
  crit : critDist (A ⊔ B) A B V = m + 1
  seven_le : 7 ≤ m
  odd : Odd m
  geo : IsGeo p (m + 1)
  start : p 0 = γ₀ (A ⊔ B) A B
  not_le : ¬ V ≤ ballStab 1 (p (m + 1))

namespace EvenCrit

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p)

include e

theorem vt_false {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : vtype (p i) = false :=
  e.geo.vtype_false_of_even rfl e.start hi he

theorem vt_true {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : vtype (p i) = true :=
  e.geo.vtype_true_of_odd rfl e.start hi ho

theorem adj {i j : ℕ} (hj : j = i + 1) (hi : i < m + 1) :
    (graph (A ⊔ B) A B).Adj (p i) (p j) := by
  subst hj
  exact e.geo.adj hi

theorem dist_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1) :
    CosetGeom.dist (p i) (p j) = j - i := e.geo i j hij hj

end EvenCrit

namespace GoldHyp3

variable [Finite D] (h : GoldHyp3 A B z V)

include h

theorem exists_c_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    ∃ c : D, c ≠ 1 ∧ c ∈ Zv z (p 1) ∧ c ∈ Zv z (p m) :=
  h.coincidence_even e.crit e.geo e.start e.not_le (e.vt_false le_rfl e.odd.add_one)

theorem Zv_eq_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    Zv z (p m) = Zv z (p 1) := by
  obtain ⟨c, hc1, hc1', hcm⟩ := h.exists_c_even e
  have h1t : vtype (p 1) = true := e.vt_true (by have := e.seven_le; omega) odd_one
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  exact le_antisymm (le_of_card_two_of_mem (h.card_Zv hmt) hcm hc1' hc1)
    (le_of_card_two_of_mem (h.card_Zv h1t) hc1' hcm hc1)

omit [Finite D] in
theorem Zv_le_W_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    Zv z (p 1) ≤ Vn V 2 (p 0) := by
  have h0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  exact (h.Zv_le_Vv (e.adj (i := 0) (j := 1) rfl (by omega)) h0).trans
    (Vv_le_Vn h0 (by rw [CosetGeom.dist_self]; omega))

theorem W_le_centralizer_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn e.crit (by rw [CosetGeom.dist_self]; have := e.seven_le; omega)

theorem good_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  have hm := e.seven_le
  refine h.le_ballStab_one_desc e.geo (i := m - 1) (by omega) (by omega) ?_ ?_
  · refine h.Vn_le_ballStab_one e.crit ?_
    have := e.dist_eq (i := 0) (j := m - 1 - 1) (Nat.zero_le _) (by omega)
    omega
  · rw [show m - 1 + 1 = m by omega, Zlab_of_vtype_true (e.vt_true (by omega) e.odd),
      h.Zv_eq_even e]
    exact (h.W_le_centralizer_even e).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (h.Zv_le_W_even e)))

theorem Vv_le_W_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p)
    (hbad : ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m)) : Vv V (p (m - 1)) ≤ Vn V 2 (p 0) := by
  have hm := e.seven_le
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  have hm1t : vtype (p (m - 1)) = false :=
    e.vt_false (by omega) (by obtain ⟨k, hk⟩ := e.odd; exact ⟨k, by omega⟩)
  have hadjm : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := e.adj (by omega) (by omega)
  obtain ⟨g0, hg0W, hg0n⟩ := IsConcreteLE.not_le_iff_exists.mp hbad
  have hg0a : g0 ∈ ballStab 1 (p (m - 1)) := h.good_even e hg0W
  have hg0s : g0 ∈ stab (p (m - 1)) := ballStab_le_stab 1 _ hg0a
  have hdm : CosetGeom.dist (p (m - 1)) (p m) ≤ 1 := by
    have := e.dist_eq (i := m - 1) (j := m) (by omega) (by omega)
    omega
  have hg0m : g0 ∈ stab (p m) := ballStab_le_stab_of_dist_le (n := 1) hdm hg0a
  have hnc : ¬ ∀ w ∈ Vv V (p m), g0 * w * g0⁻¹ * w⁻¹ ∈ Zv z (p m) := fun hall =>
    hg0n (h.mem_ballStab_one_of_commutator hmt hg0m hall)
  push Not at hnc
  obtain ⟨w, hw, hwn⟩ := hnc
  have hc'V : g0 * w * g0⁻¹ * w⁻¹ ∈ Vv V (p (m - 1)) :=
    h.commutator_mem_Vv e.card_eq hadjm hm1t ⟨hg0s, hg0m⟩ hw
  have hw1 : w ∈ ballStab 1 (p 1) := by
    have hd : CosetGeom.dist (p m) (p 1) + 1 ≤ m := by
      have := e.dist_eq (i := 1) (j := m) (by omega) (by omega)
      rw [CosetGeom.dist_comm]
      omega
    exact h.VvB_le_ballStab_one_of_dist e.crit hmt hd hw
  have hw0 : w ∈ stab (p 0) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hw1
    have := e.dist_eq (i := 0) (j := 1) (by omega) (by omega)
    rw [CosetGeom.dist_comm]
    omega
  have hwn' := h.stab_le_normalizer_Vn 2 (p 0) hw0
  have hwg : w * g0⁻¹ * w⁻¹ ∈ Vn V 2 (p 0) :=
    (Subgroup.mem_normalizer_iff.mp hwn' g0⁻¹).mp ((Vn V 2 (p 0)).inv_mem hg0W)
  have hc'W : g0 * w * g0⁻¹ * w⁻¹ ∈ Vn V 2 (p 0) := by
    have : g0 * w * g0⁻¹ * w⁻¹ = g0 * (w * g0⁻¹ * w⁻¹) := by group
    rw [this]
    exact (Vn V 2 (p 0)).mul_mem hg0W hwg
  refine le_of_card_four (h.card_Vv_A hm1t) (h.card_Zv hmt) (h.Zv_le_Vv hadjm hm1t) ?_ hc'V hc'W hwn
  rw [h.Zv_eq_even e]
  exact h.Zv_le_W_even e

theorem X_le_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p)
    (hV : Vv V (p (m - 1)) ≤ Vn V 2 (p 0)) : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  have hm := e.seven_le
  have hXW : Vn V 4 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
    h.Vn_le_centralizer_Vn e.crit (by rw [CosetGeom.dist_self]; omega)
  have cent : ∀ Y : Subgroup D, Y ≤ Vn V 2 (p 0) →
      Vn V 4 (p 0) ≤ Subgroup.centralizer (Y : Set D) := fun Y hY =>
    hXW.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hY))
  have hm1t : vtype (p (m - 1)) = false :=
    e.vt_false (by omega) (by obtain ⟨k, hk⟩ := e.odd; exact ⟨k, by omega⟩)
  have hm2t : vtype (p (m - 2)) = true :=
    e.vt_true (by omega) (by obtain ⟨k, hk⟩ := e.odd; exact ⟨k - 1, by omega⟩)
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  have hZ2 : Zv z (p (m - 2)) ≤ Vn V 2 (p 0) :=
    (h.Zv_le_Vv (e.adj (i := m - 2) (j := m - 1) (by omega) (by omega)).symm hm1t).trans hV
  have s1 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 3)) := by
    refine h.le_ballStab_one_desc e.geo (i := m - 3) (by omega) (by omega) ?_ ?_
    · refine h.Vn_le_ballStab_one e.crit ?_
      have := e.dist_eq (i := 0) (j := m - 3 - 1) (Nat.zero_le _) (by omega)
      omega
    · rw [show m - 3 + 1 = m - 2 by omega, Zlab_of_vtype_true hm2t]
      exact cent _ hZ2
  have s2 : Vn V 4 (p 0) ≤ ballStab 1 (p (m - 2)) := by
    refine h.le_ballStab_one_desc e.geo (i := m - 2) (by omega) (by omega) ?_ ?_
    · rw [show m - 2 - 1 = m - 3 by omega]
      exact s1
    · rw [show m - 2 + 1 = m - 1 by omega, Zlab_of_vtype_false hm1t]
      exact cent _ hV
  refine h.le_ballStab_one_desc e.geo (i := m - 1) (by omega) (by omega) ?_ ?_
  · rw [show m - 1 - 1 = m - 2 by omega]
    exact s2
  · rw [show m - 1 + 1 = m by omega, Zlab_of_vtype_true hmt, h.Zv_eq_even e]
    exact cent _ (h.Zv_le_W_even e)

theorem exists_far_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    ∃ v ∈ Vv V (p (m + 1)), v ∉ ballStab 1 (p 0) := by
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

theorem Vv_far_le_stab_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    Vv V (p (m + 1)) ≤ stab (p 0) ⊓ stab (p 1) := by
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

theorem not_W_le_Q_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) :
    ¬ Vn V 2 (p 0) ≤ ballStab 1 (p m) := by
  intro hW
  have hm := e.seven_le
  have hv0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have h1t : vtype (p 1) = true := e.vt_true (by omega) odd_one
  have hmt : vtype (p m) = true := e.vt_true (by omega) e.odd
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := e.adj (i := 0) (j := 1) rfl (by omega)
  obtain ⟨v, hv, hvn⟩ := h.exists_far_even e
  have hvT := h.Vv_far_le_stab_even e hv
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
      (by rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hmm]) hwq |> fun x => x
    have hwb : w ∈ stab (p m) := ballStab_le_stab 1 _ hwq
    have hc := h.commutator_mem_Zv hmm hev ⟨hwa, hwb⟩ hv
    have hinv : v * w * v⁻¹ * w⁻¹ = (w * v * w⁻¹ * v⁻¹)⁻¹ := by group
    rw [hinv]
    refine Vv V (p 0) |>.inv_mem ?_
    have : w * v * w⁻¹ * v⁻¹ ∈ Zv z (p 1) := by rw [← h.Zv_eq_even e]; exact hc
    exact h.Zv_le_Vv h01 hv0 this
  have hbot := h.eq_bot_of_acts_trivially h01 hYZ hZY hZT
    (stab_le_normalizer_Vv h.natural.reduced.2.1 (p 0)) (h.stab_le_normalizer_Vn 2 (p 0))
    (stab_le_normalizer_Vv h.natural.reduced.2.1 (p 1)) hvT hvn hcomm
  have hc := h.card_Vv_B e.card_eq h1t
  rw [hbot] at hc
  simp at hc

theorem false_of_even {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (e : EvenCrit V m p) : False := by
  have hm := e.seven_le
  have hbad := h.not_W_le_Q_even e
  have hV := h.Vv_le_W_even e hbad
  have hX := h.X_le_even e hV
  have hv0 : vtype (p 0) = false := e.vt_false (by omega) ⟨0, rfl⟩
  have hev : vtype (p (m + 1)) = false := e.vt_false le_rfl e.odd.add_one
  have hm1t : vtype (p (m - 1)) = false :=
    e.vt_false (by omega) (by obtain ⟨k, hk⟩ := e.odd; exact ⟨k, by omega⟩)
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := e.adj (i := 0) (j := 1) rfl (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p (m + 1)) (p m) :=
    (e.adj (i := m) (j := m + 1) rfl (by omega)).symm
  have hadj : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := e.adj (by omega) (by omega)
  obtain ⟨v, hv, hvn⟩ := h.exists_far_even e
  have hvT := h.Vv_far_le_stab_even e hv
  have hd01 : CosetGeom.dist (p 1) (p 0) = 1 := by
    rw [CosetGeom.dist_comm]
    exact CosetGeom.dist_eq_one_iff_adj.mpr h01
  have hWZ : Vn V 2 (p 0) ≤ Vn V 3 (p 1) := by
    refine Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl ?_
    have := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 1) (p 0) l
    omega
  have hZX : Vn V 3 (p 1) ≤ Vn V 4 (p 0) := by
    refine Vn_le_iff.mpr fun l hl hd => Vv_le_Vn hl ?_
    have := CosetGeom.dist_triangle (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) rfl (p 0) (p 1) l
    rw [CosetGeom.dist_comm (p 0) (p 1)] at this
    omega
  have hZT : Vn V 3 (p 1) ≤ stab (p 0) ⊓ stab (p 1) := by
    refine le_inf ((h.Vn_le_ballStab_one e.crit (x := p 1) (y := p 0) (n := 3) ?_).trans
      (ballStab_le_stab 1 _)) ((h.Vn_le_ballStab_one e.crit (x := p 1) (y := p 1) (n := 3)
      ?_).trans (ballStab_le_stab 1 _))
    · omega
    · rw [CosetGeom.dist_self]
      omega
  have hcomm : ∀ w ∈ Vn V 4 (p 0), v * w * v⁻¹ * w⁻¹ ∈ Vn V 2 (p 0) := by
    intro w hw
    have hwq := hX hw
    have hwa : w ∈ stab (p (m - 1)) := ballStab_le_stab 1 _ hwq
    have hd : CosetGeom.dist (p (m - 1)) (p m) ≤ 1 :=
      (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le
    have hwb : w ∈ stab (p m) := ballStab_le_stab_of_dist_le (n := 1) hd hwq
    have hvm : v ∈ Vv V (p m) := Vv_le_Vv_of_adj hmm hev hv
    have hc := h.commutator_mem_Vv e.card_eq hadj hm1t ⟨hwa, hwb⟩ hvm
    have hinv : v * w * v⁻¹ * w⁻¹ = (w * v * w⁻¹ * v⁻¹)⁻¹ := by group
    rw [hinv]
    exact (Vn V 2 (p 0)).inv_mem (hV hc)
  have hbot := h.eq_bot_of_acts_trivially h01 hWZ hZX hZT (h.stab_le_normalizer_Vn 2 (p 0))
    (h.stab_le_normalizer_Vn 4 (p 0)) (h.stab_le_normalizer_Vn 3 (p 1)) hvT hvn hcomm
  have h0Z : Vv V (p 0) ≤ Vn V 3 (p 1) := Vv_le_Vn hv0 (by omega)
  have hc := Subgroup.card_le_of_le h0Z
  rw [h.card_Vv_A hv0, hbot] at hc
  simp at hc

theorem false_of_even_critDist (hU : Nat.card (conjClosure V B) = 8) {m : ℕ}
    (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 7 ≤ m) (hmo : Odd m) : False := by
  obtain ⟨p, hp0, hgeo, hnle⟩ := h.exists_crit_geodesic hb
  exact h.false_of_even ⟨hU, hb, hm, hmo, hgeo, hp0, hnle⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
