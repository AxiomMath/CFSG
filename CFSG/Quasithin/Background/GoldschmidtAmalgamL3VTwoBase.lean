module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3VBase

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure TypeIIConfig (V : Subgroup D) (m : ℕ) (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  card : Nat.card (conjClosure V B) = 8
  critDist_eq : critDist (A ⊔ B) A B V = m + 1
  eight_le : 8 ≤ m
  even : Even m
  geo : IsGeo p (m + 1)
  vtype_zero : vtype (p 0) = false
  crit : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1))
  typeII : ¬ Vv V (p (m + 1)) ≤ ballStab 1 (p 1)

namespace TypeIIConfig

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : TypeIIConfig V m p)

include c

theorem vtype_even {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : vtype (p i) = false :=
  c.geo.vtype_false_of_even_start rfl c.vtype_zero hi he

theorem vtype_odd {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : vtype (p i) = true :=
  c.geo.vtype_true_of_odd_start rfl c.vtype_zero hi ho

theorem adj {i : ℕ} (hi : i ≤ m) : (graph (A ⊔ B) A B).Adj (p i) (p (i + 1)) :=
  c.geo.adj (by omega)

theorem adj' {i j : ℕ} (hij : j = i + 1) (hj : j ≤ m + 1) :
    (graph (A ⊔ B) A B).Adj (p i) (p j) := by
  subst hij
  exact c.adj (by omega)

theorem adj_pred {i : ℕ} (hi : i ≤ m + 1) (h1 : 1 ≤ i) :
    (graph (A ⊔ B) A B).Adj (p i) (p (i - 1)) := by
  have := c.adj (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at this
  exact this.symm

theorem dist_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1) : CosetGeom.dist (p i) (p j) = j - i := by
  rw [c.geo i j hij hj]

theorem Vv_ne_bot (h : GoldHyp3 A B z V) {i : ℕ} (hi : i ≤ m + 1) (he : Even i) :
    Vv V (p i) ≠ ⊥ := fun e => by
  have := h.card_Vv_A (c.vtype_even hi he)
  rw [e, Subgroup.card_bot] at this
  omega

variable [Finite D]

theorem exists_u (h : GoldHyp3 A B z V) :
    ∃ u : D, u ∈ Vv V (p (m + 1)) ∧ u ∈ ballStab 1 (p 2) ∧ u ∈ stab (p 1) ⊓ stab (p 2) ∧
      u ∉ ballStab 1 (p 1) := by
  have hm := c.eight_le
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  obtain ⟨u, huV, huQ⟩ := IsConcreteLE.not_le_iff_exists.1 c.typeII
  have hu2 : u ∈ ballStab 1 (p 2) := by
    refine h.VvB_le_ballStab_one_of_dist c.critDist_eq hbt ?_ huV
    rw [CosetGeom.dist_comm, c.dist_eq (i := 2) (j := m + 1) (by omega) le_rfl]
    omega
  refine ⟨u, huV, hu2, ⟨?_, ballStab_le_stab 1 _ hu2⟩, huQ⟩
  refine ballStab_le_stab_of_dist_le (n := 1) ?_ hu2
  rw [CosetGeom.dist_comm, c.dist_eq (i := 1) (j := 2) (by omega) (by omega)]

theorem exists_c (h : GoldHyp3 A B z V) :
    ∃ x : D, x ≠ 1 ∧ x ∈ Vv V (p 2) ∧ x ∈ Vv V (p m) ∧ x ∉ Zv z (p 1) := by
  have hm := c.eight_le
  have hodd : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have hv1 : vtype (p 1) = true := c.vtype_odd (by omega) odd_one
  obtain ⟨γ, hγ, hnot⟩ : ∃ γ, (graph (A ⊔ B) A B).Adj (p (m + 1)) γ ∧
      ¬ Vv V γ ≤ ballStab 1 (p 1) := by
    by_contra hcon
    push Not at hcon
    exact c.typeII ((Vv_B_le_iff hodd).mpr hcon)
  have h12 : (graph (A ⊔ B) A B).Adj (p 1) (p 2) := c.adj (i := 1) (by omega)
  have hmm : (graph (A ⊔ B) A B).Adj (p m) (p (m + 1)) := c.adj le_rfl
  have hγt : vtype γ = false := vtype_eq_false_of_adj hγ hodd
  obtain ⟨w, hwγ, hwn⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hw : w ∈ Vv V (p (m + 1)) := Vv_le_Vv_of_adj hγ.symm hγt hwγ
  have hd1 : CosetGeom.dist (p 1) (p (m + 1)) ≤ m := by
    rw [c.dist_eq (by omega) le_rfl]
    omega
  have hd2 : CosetGeom.dist (p 1) (p m) ≤ m := by
    rw [c.dist_eq (by omega) (by omega)]
    omega
  have hd3 : CosetGeom.dist (p (m + 1)) (p 1) ≤ m := by
    rw [CosetGeom.dist_comm]
    exact hd1
  have hd4 : CosetGeom.dist (p (m + 1)) (p 2) ≤ m := by
    rw [CosetGeom.dist_comm, c.dist_eq (by omega) le_rfl]
    omega
  have hwb : w ∈ stab (p 1) := h.Vv_le_stab_B c.critDist_eq hodd hd3 hw
  have hnc : ¬ ∀ x ∈ Vv V (p 1), w * x * w⁻¹ * x⁻¹ ∈ Zv z (p 1) := fun hall =>
    hwn (h.mem_ballStab_one_of_commutator hv1 hwb hall)
  push Not at hnc
  obtain ⟨x, hx, hxw⟩ := hnc
  have e : w * x * w⁻¹ * x⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by group
  have hc1 : x * w * x⁻¹ * w⁻¹ ≠ 1 := fun e1 =>
    hxw (by rw [e, e1, inv_one]; exact (Zv z (p 1)).one_mem)
  have hmem := h.commutator_mem_Vv_inf c.card c.critDist_eq hv1 hodd h12 hmm.symm hd1 hd2 hd3 hd4
    hx hw
  refine ⟨x * w * x⁻¹ * w⁻¹, hc1, hmem.1, hmem.2, fun hc => hxw ?_⟩
  rw [e]
  exact (Zv z (p 1)).inv_mem hc

end TypeIIConfig

theorem Vn_one_eq_Vv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    Vn V 1 v = Vv V v := by
  refine le_antisymm (Vn_le_iff.mpr fun l hl hd => ?_) ((Vv_B_le_iff hv).mpr fun l hl => ?_)
  · rcases (dist_le_one_iff rfl).mp hd with e | hadj
    · rw [e] at hv
      exact absurd hv (by simp [hl])
    · exact Vv_le_Vv_of_adj hadj.symm hl
  · exact Vv_le_Vn (vtype_eq_false_of_adj hl hv) (dist_eq_one_iff_adj.mpr hl).le

end GoldAmL3

end F6

end CFSG.Quasithin
