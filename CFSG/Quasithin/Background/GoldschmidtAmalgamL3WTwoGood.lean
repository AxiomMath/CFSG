module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WInt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure OddCritG {D : Type*} [Group D] {A B : Subgroup D} (V : Subgroup D) (m : ℕ)
    (p : ℕ → CosetGeom (A ⊔ B) A B) : Prop where
  crit_eq : critDist (A ⊔ B) A B V = m + 1
  six_le : 6 ≤ m
  even : Even m
  start : p 0 = γ₀ (A ⊔ B) A B
  geo : IsGeo p (m + 1)
  crit : ¬ V ≤ ballStab 1 (p (m + 1))

namespace OddCritG

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : OddCritG V m p)

include c

theorem vtype_zero : vtype (p 0) = false := by
  rw [c.start]
  exact vtype_γ₀

theorem vtype_even {i : ℕ} (hi : i ≤ m + 1) (he : Even i) : vtype (p i) = false :=
  c.geo.vtype_false_of_even_start rfl c.vtype_zero hi he

theorem vtype_odd {i : ℕ} (hi : i ≤ m + 1) (ho : Odd i) : vtype (p i) = true :=
  c.geo.vtype_true_of_odd_start rfl c.vtype_zero hi ho

theorem adj {i : ℕ} (hi : i ≤ m) : (graph (A ⊔ B) A B).Adj (p i) (p (i + 1)) :=
  c.geo.adj (by omega)

theorem adj_pred {i : ℕ} (hi : i ≤ m + 1) (h1 : 1 ≤ i) :
    (graph (A ⊔ B) A B).Adj (p i) (p (i - 1)) := by
  have := c.adj (i := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at this
  exact this.symm

theorem dist_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1) :
    CosetGeom.dist (p i) (p j) = j - i := c.geo i j hij hj

theorem ne {i j : ℕ} (hij : i < j) (hj : j ≤ m + 1) : p i ≠ p j := c.geo.ne hij hj

theorem Vv_zero (h : GoldHyp3 A B z V) : Vv V (p 0) = V := by
  rw [c.start]
  exact Vv_γ₀ h.natural.reduced.2.1

theorem crit' (h : GoldHyp3 A B z V) : ¬ Vv V (p 0) ≤ ballStab 1 (p (m + 1)) := by
  rw [c.Vv_zero h]
  exact c.crit

end OddCritG

variable [Finite D]

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem mem_Zv_of_swap_at_A (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    {a t : CosetGeom (A ⊔ B) A B} (ha : vtype a = false) (hat : (graph (A ⊔ B) A B).Adj a t)
    {g : D} (hga : g ∈ stab a) (hgt : g ∉ stab t) {c : D} (hc : c ∈ Theta z V a t)
    (hgc : g * c * g⁻¹ = c) : c ∈ Zv z t := by
  have htt : vtype t = true := vtype_eq_true_of_adj hat ha
  have hgG : g ∈ A ⊔ B := stab_le a hga
  lift g to ↥(A ⊔ B) using hgG with g'
  have hg'a : g' • a = a := smul_eq_of_mem_stab hga
  have hg't : g' • t ≠ t := fun e => hgt (mem_stab_of_smul_eq e)
  have hadj : (graph (A ⊔ B) A B).Adj a (g' • t) := by
    have := (smul_adj g').mpr hat
    rwa [hg'a] at this
  have hc' : c ∈ Theta z V a (g' • t) := by
    have e := h.Theta_smul g' a t
    rw [hg'a] at e
    rw [e, mem_conjSub]
    rw [inv_mul_mul_of_mul_mul_inv hgc]
    exact hc
  have h1 : c ∈ Vv V t := h.Theta_le_Vv ha hat hc
  have h2 : c ∈ Vv V (g' • t) := h.Theta_le_Vv ha hadj hc'
  have h3 : c ∈ Vv V a := hI1 a t (g' • t) ha hat hadj (Ne.symm hg't) ⟨h1, h2⟩
  have hmem : c ∈ Theta z V a t ⊓ Vv V a := ⟨hc, h3⟩
  rwa [h.Theta_inf_Vv ha hat (h.card_Vv_B_of_card hU htt)] at hmem

theorem mem_Zv_of_swap_at_B (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2 : I2aProp A B V)
    {a t β : CosetGeom (A ⊔ B) A B} (ha : vtype a = false) (hat : (graph (A ⊔ B) A B).Adj a t)
    (haβ : (graph (A ⊔ B) A B).Adj a β) (htβ : t ≠ β) {g : D} (hgβ : g ∈ stab β)
    (hga : g ∉ stab a) {c : D} (hc : c ∈ Theta z V a t) (hgc : g * c * g⁻¹ = c) :
    c ∈ Zv z t := by
  have htt : vtype t = true := vtype_eq_true_of_adj hat ha
  have hβt : vtype β = true := vtype_eq_true_of_adj haβ ha
  have hgG : g ∈ A ⊔ B := stab_le β hgβ
  lift g to ↥(A ⊔ B) using hgG with g'
  have hg'β : g' • β = β := smul_eq_of_mem_stab hgβ
  have hg'a : g' • a ≠ a := fun e => hga (mem_stab_of_smul_eq e)
  have hadj : (graph (A ⊔ B) A B).Adj β (g' • a) := by
    have := (smul_adj g').mpr haβ.symm
    rwa [hg'β] at this
  have hga_t : vtype (g' • a) = false := by rwa [vtype_smul]
  have hadj2 : (graph (A ⊔ B) A B).Adj (g' • a) (g' • t) := (smul_adj g').mpr hat
  have hc' : c ∈ Theta z V (g' • a) (g' • t) := by
    rw [h.Theta_smul g' a t, mem_conjSub, inv_mul_mul_of_mul_mul_inv hgc]
    exact hc
  have h1 : c ∈ Vv V t := h.Theta_le_Vv ha hat hc
  have h2 : c ∈ Vv V (g' • t) := h.Theta_le_Vv hga_t hadj2 hc'
  have hgtβ : g' • t ≠ β := fun e => htβ (smul_left_cancel g' (e.trans hg'β.symm))
  have h3 : c ∈ Vv V β :=
    hI2 β a (g' • a) t (g' • t) hβt haβ.symm hadj (Ne.symm hg'a) hat hadj2 htβ hgtβ ⟨h1, h2⟩
  have h5 : c ∈ Vv V a := hI1 a t β ha hat haβ htβ ⟨h1, h3⟩
  have hmem : c ∈ Theta z V a t ⊓ Vv V a := ⟨hc, h5⟩
  rwa [h.Theta_inf_Vv ha hat (h.card_Vv_B_of_card hU htt)] at hmem

end GoldHyp3

namespace OddCritG

variable {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : OddCritG V m p) (h : GoldHyp3 A B z V)

include c h

theorem exists_comm_elt :
    ∃ x : D, x ∈ Vn V 2 (p 0) ∧ x ∈ Theta z V (p m) (p (m + 1)) ∧ x ∉ Zv z (p (m + 1)) := by
  have hm := c.six_le
  have hb := c.crit_eq
  have hbt : vtype (p (m + 1)) = true := c.vtype_odd le_rfl c.even.add_one
  have h0 : vtype (p 0) = false := c.vtype_zero
  have h2t : vtype (p 2) = false := c.vtype_even (by omega) even_two
  have hdm : CosetGeom.dist (p 0) (p m) + 1 ≤ m + 1 := by
    rw [c.dist_eq (Nat.zero_le _) (by omega)]
    omega
  obtain ⟨x₀, hx₀V, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.crit' h)
  have hx₀b : x₀ ∈ stab (p (m + 1)) :=
    h.Vv_le_stab_A hb h0 (by rw [c.dist_eq (Nat.zero_le _) le_rfl]; omega) hx₀V
  have hx₀m : x₀ ∈ ballStab 1 (p m) := h.Vv_le_ballStab_one_of_dist hb h0 hdm hx₀V
  obtain ⟨w, hw, hnc⟩ : ∃ w ∈ Vv V (p (m + 1)), x₀ * w * x₀⁻¹ * w⁻¹ ∉ Zv z (p (m + 1)) := by
    by_contra hcon
    push Not at hcon
    exact hx₀Q (h.mem_ballStab_one_of_commutator hbt hx₀b hcon)
  have hw2 : w ∈ ballStab 1 (p 2) := by
    refine h.VvB_le_ballStab_one_of_dist hb hbt ?_ hw
    rw [CosetGeom.dist_comm, c.dist_eq (i := 2) (j := m + 1) (by omega) le_rfl]
    omega
  have hw12 : w ∈ stab (p 2) ⊓ stab (p 1) := by
    refine ⟨ballStab_le_stab 1 _ hw2, ballStab_le_stab_of_dist_le (n := 1) ?_ hw2⟩
    rw [CosetGeom.dist_comm, c.dist_eq (i := 1) (j := 2) (by omega) (by omega)]
  have h01 : (graph (A ⊔ B) A B).Adj (p 0) (p 1) := c.adj (i := 0) (by omega)
  have hx₀1 : x₀ ∈ Vv V (p 1) := Vv_le_Vv_of_adj h01 h0 hx₀V
  have hth : w * x₀ * w⁻¹ * x₀⁻¹ ∈ Theta z V (p 2) (p 1) := comm_mem_Theta hw12 hx₀1 z
  have hadj21 : (graph (A ⊔ B) A B).Adj (p 2) (p 1) := (c.adj (i := 1) (by omega)).symm
  have hW : w * x₀ * w⁻¹ * x₀⁻¹ ∈ Vn V 2 (p 0) :=
    Vv_B_le_Vn_two h0 h01 (h.Theta_le_Vv h2t hadj21 hth)
  refine ⟨x₀ * w * x₀⁻¹ * w⁻¹, ?_, comm_mem_Theta ⟨ballStab_le_stab 1 _ hx₀m, hx₀b⟩ hw z, hnc⟩
  have e : x₀ * w * x₀⁻¹ * w⁻¹ = (w * x₀ * w⁻¹ * x₀⁻¹)⁻¹ := by group
  rw [e]
  exact (Vn V 2 (p 0)).inv_mem hW

theorem Vn_two_abelian : Vn V 2 (p 0) ≤ Subgroup.centralizer (Vn V 2 (p 0) : Set D) :=
  h.Vn_le_centralizer_Vn c.crit_eq (by rw [CosetGeom.dist_self]; have := c.six_le; omega)

theorem comm_of_mem_Vn_two {g x : D} (hg : g ∈ Vn V 2 (p 0)) (hx : x ∈ Vn V 2 (p 0)) :
    g * x * g⁻¹ = x :=
  mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp (c.Vn_two_abelian h hg) x hx).symm

theorem Vn_two_le_ballStab_pred (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hI2 : I2aProp A B V) :
    Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1)) := by
  intro g hg
  by_contra hgQ
  have hm := c.six_le
  have hb := c.crit_eq
  obtain ⟨x, hxW, hxΘ, hxZ⟩ := c.exists_comm_elt h
  have hat : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hg2 : g ∈ ballStab 1 (p (m - 2)) := by
    refine h.Vn_le_ballStab_one hb ?_ hg
    rw [c.dist_eq (Nat.zero_le _) (by omega)]
    omega
  have hg2s : g ∈ stab (p (m - 2)) := ballStab_le_stab 1 _ hg2
  have hgβ : g ∈ stab (p (m - 1)) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hg2
    rw [c.dist_eq (i := m - 2) (j := m - 1) (by omega) (by omega)]
    omega
  have hβ2 : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p (m - 2)) := by
    have := c.adj_pred (i := m - 1) (by omega) (by omega)
    rwa [show m - 1 - 1 = m - 2 by omega] at this
  have hβm : (graph (A ⊔ B) A B).Adj (p (m - 1)) (p m) := by
    have := c.adj (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have hga : g ∉ stab (p m) := fun hgm =>
    hgQ (h.mem_ballStab_one_of_fix_two' hβ2 hβm (c.ne (i := m - 2) (j := m) (by omega) (by omega))
      hgβ hg2s hgm)
  have hgc : g * x * g⁻¹ = x := c.comm_of_mem_Vn_two h hg hxW
  exact hxZ (h.mem_Zv_of_swap_at_B hU hI1 hI2 hat (c.adj le_rfl) (c.adj_pred (by omega) (by omega))
    (c.ne (i := m - 1) (j := m + 1) (by omega) le_rfl).symm hgβ hga hxΘ hgc)

theorem Vn_two_le_ballStab_last (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hgood : Vn V 2 (p 0) ≤ ballStab 1 (p (m - 1))) :
    Vn V 2 (p 0) ≤ ballStab 1 (p m) := by
  intro g hg
  by_contra hgQ
  have hm := c.six_le
  obtain ⟨x, hxW, hxΘ, hxZ⟩ := c.exists_comm_elt h
  have hat : vtype (p m) = false := c.vtype_even (by omega) c.even
  have hg1 : g ∈ ballStab 1 (p (m - 1)) := hgood hg
  have hgm1 : g ∈ stab (p (m - 1)) := ballStab_le_stab 1 _ hg1
  have hgm : g ∈ stab (p m) := by
    refine ballStab_le_stab_of_dist_le (n := 1) ?_ hg1
    rw [c.dist_eq (i := m - 1) (j := m) (by omega) (by omega)]
    omega
  have hmm1 : (graph (A ⊔ B) A B).Adj (p m) (p (m - 1)) := c.adj_pred (by omega) (by omega)
  have hgt : g ∉ stab (p (m + 1)) := fun hgt =>
    hgQ (h.mem_ballStab_one_of_fix_two' hmm1 (c.adj le_rfl)
      (c.ne (i := m - 1) (j := m + 1) (by omega) le_rfl) hgm hgm1 hgt)
  have hgc : g * x * g⁻¹ = x := c.comm_of_mem_Vn_two h hg hxW
  exact hxZ (h.mem_Zv_of_swap_at_A hU hI1 hat (c.adj le_rfl) hgm hgt hxΘ hgc)

end OddCritG

end GoldAmL3

end F6

end CFSG.Quasithin
