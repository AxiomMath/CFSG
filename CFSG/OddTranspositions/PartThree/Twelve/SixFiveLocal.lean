module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
import CFSG.OddTranspositions.PartFour.Fourteen.FiveRigid
import CFSG.OddTranspositions.PartThree.CommSetConj
import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace FiveChart

open CFSG.OddTranspositions.PartFour.TableE1Five

variable {hC : HypothesisC D} {n : ℕ}

omit [Finite G] in
private theorem act_refl_sub (c : FiveChart hC n) {x : G} (hx : x ∈ commSet D hC.d)
    (y : Fin n → ZMod 5) :
    act (refl c.b (c.vec x)) y = y - (2 * c.b y (c.vec x)) • c.vec x := by
  rw [act_refl (c.norm_vec x hx)]
  module

omit [Finite G] in
private theorem exists_pivot {w v : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hv : v ∈ commSet D hC.d ∩ commSet D w) :
    ∃ h : G, h * v * h⁻¹ = hC.d ∧
      h * hC.d * h⁻¹ ∈ commSet D hC.d ∧ h * w * h⁻¹ ∈ commSet D hC.d ∧
      h * hC.d * h⁻¹ ≠ h * w * h⁻¹ ∧
      ¬ Commute (h * hC.d * h⁻¹) (h * w * h⁻¹) := by
  obtain ⟨h, hh⟩ := isConj_iff.mp (hC.setup.isConj hv.1.1 hC.hd)
  have hdmem : hC.d ∈ commSet D v := ⟨hC.hd, hv.1.2.1.symm, hv.1.2.2.symm⟩
  have hwmem : w ∈ commSet D v := ⟨hw, hv.2.2.1.symm, hv.2.2.2.symm⟩
  refine ⟨h, hh, by simpa [hh] using conj_mem_commSet hC.setup.normal h hdmem,
    by simpa [hh] using conj_mem_commSet hC.setup.normal h hwmem, ?_, ?_⟩
  · intro hEq
    have hdw : hC.d = w := conj_injective (x := h) hEq
    exact hwd (by rw [← hdw])
  · intro hc
    exact hwd ((Commute.conj_iff h).mp hc).symm

private theorem sq_eq_four_of_ne_zero_of_ne_one (t : ZMod 5) (h0 : t ≠ 0) (h1 : t ^ 2 ≠ 1) :
    t ^ 2 = 4 := by
  revert h0 h1
  revert t
  decide

private theorem sq_eq_sq_of_ne_zero (a c : ZMod 5) (ha : a ≠ 0) (hc : c ≠ 0)
    (h : a ^ 2 = 1 ↔ c ^ 2 = 1) : a ^ 2 = c ^ 2 := by
  revert ha hc h
  revert a c
  decide

omit [Finite G] in
private theorem vec_norm_perp_pivot (c : FiveChart hC n) {v : G}
    (hv : v ∈ commSet D hC.d) :
    ∀ x ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec x) (c.vec x) = 1 ∧ c.b (c.vec x) (c.vec v) = 0 := by
  intro x hx
  exact ⟨c.norm_vec x hx.1,
    (c.commute_iff x hx.1 v hv hx.2.2.2).mp hx.2.2.1⟩

omit [Finite G] in
private theorem vec_conj_norm_perp_pivot (c : FiveChart hC n) {v h : G}
    (hh : h * v * h⁻¹ = hC.d)
    (hP : h * hC.d * h⁻¹ ∈ commSet D hC.d) :
    ∀ x ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * x * h⁻¹)) = 1 ∧
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) = 0 := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hx.2
  refine ⟨c.norm_vec _ hx', ?_⟩
  have hne : h * x * h⁻¹ ≠ h * hC.d * h⁻¹ :=
    fun hEq => hx.1.2.2 (conj_injective (x := h) hEq)
  exact (c.commute_iff _ hx' _ hP hne).mp (hx.1.2.1.conj h)

omit [Finite G] in
private theorem exists_mem_inter_vec (c : FiveChart hC n) {v : G}
    (hv : v ∈ commSet D hC.d) :
    ∀ y : Fin n → ZMod 5, c.b y y = 1 → c.b y (c.vec v) = 0 →
      ∃ x ∈ commSet D hC.d ∩ commSet D v, c.vec x = y ∨ c.vec x = -y := by
  intro y hy1 hyv
  obtain ⟨z₀, hz₀mem, hz₀vec⟩ := c.exists_vec y hy1
  have hperp : c.b (c.vec z₀) (c.vec v) = 0 := by
    rcases hz₀vec with h | h
    · rw [h]; exact hyv
    · rw [h, LinearMap.BilinForm.neg_left, hyv, neg_zero]
  have hne : z₀ ≠ v := by
    intro hEq
    have h1 : c.b (c.vec z₀) (c.vec v) = 1 := by
      rw [hEq, c.norm_vec v hv]
    rw [hperp] at h1
    exact (by decide : (0 : ZMod 5) ≠ 1) h1
  have hcomm : Commute z₀ v := (c.commute_iff z₀ hz₀mem v hv hne).mpr hperp
  exact ⟨z₀, ⟨hz₀mem, hz₀mem.1, hcomm, hne⟩, hz₀vec⟩

omit [Finite G] in
private theorem orderOf_conj_mul (h x y : G) :
    orderOf (h * x * h⁻¹ * (h * y * h⁻¹)) = orderOf (x * y) := by
  rw [show h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ by group]
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj h) (x * y)

omit [Finite G] in
private theorem sq_eq_one_iff_conj (c : FiveChart hC n) {v h x y : G}
    (hh : h * v * h⁻¹ = hC.d)
    (hx : x ∈ commSet D hC.d ∩ commSet D v)
    (hy : y ∈ commSet D hC.d ∩ commSet D v)
    (hxy : x ≠ y) (ha0 : c.b (c.vec x) (c.vec y) ≠ 0)
    (hb0 : c.b (c.vec (h * x * h⁻¹)) (c.vec (h * y * h⁻¹)) ≠ 0) :
    c.b (c.vec x) (c.vec y) ^ 2 = 1 ↔
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * y * h⁻¹)) ^ 2 = 1 := by
  have hx' : h * x * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hx.2
  have hy' : h * y * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hy.2
  have hne' : h * x * h⁻¹ ≠ h * y * h⁻¹ :=
    fun hEq => hxy (conj_injective (x := h) hEq)
  have h1 := c.orderOf_mul x hx.1 y hy.1 hxy ha0
  have h2 := c.orderOf_mul (h * x * h⁻¹) hx' (h * y * h⁻¹) hy' hne' hb0
  constructor
  · intro ha1
    have h5 : orderOf (x * y) = 5 := by rw [h1, if_pos ha1]
    have h5' : orderOf (h * x * h⁻¹ * (h * y * h⁻¹)) = 5 := by
      rw [orderOf_conj_mul h]; exact h5
    by_contra hc1
    rw [h2, if_neg hc1] at h5'
    exact absurd h5' (by decide)
  · intro hc1
    have h5' : orderOf (h * x * h⁻¹ * (h * y * h⁻¹)) = 5 := by
      rw [h2, if_pos hc1]
    have h5 : orderOf (x * y) = 5 := by
      rw [orderOf_conj_mul h] at h5'; exact h5'
    by_contra ha1
    rw [h1, if_neg ha1] at h5
    exact absurd h5 (by decide)

omit [Finite G] in
private theorem sq_vec_conj_eq (c : FiveChart hC n) {v h : G}
    (hh : h * v * h⁻¹ = hC.d) :
    ∀ x ∈ commSet D hC.d ∩ commSet D v, ∀ y ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec x) (c.vec y) ^ 2
        = c.b (c.vec (h * x * h⁻¹)) (c.vec (h * y * h⁻¹)) ^ 2 := by
  intro x hx y hy
  have hx' : h * x * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hx.2
  have hy' : h * y * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hy.2
  by_cases hxy : x = y
  · rw [hxy, c.norm_vec y hy.1, c.norm_vec (h * y * h⁻¹) hy']
  · have hne' : h * x * h⁻¹ ≠ h * y * h⁻¹ :=
      fun hEq => hxy (conj_injective (x := h) hEq)
    by_cases hcomm : Commute x y
    · have h1 : c.b (c.vec x) (c.vec y) = 0 :=
        (c.commute_iff x hx.1 y hy.1 hxy).mp hcomm
      have h2 : c.b (c.vec (h * x * h⁻¹)) (c.vec (h * y * h⁻¹)) = 0 :=
        (c.commute_iff _ hx' _ hy' hne').mp (hcomm.conj h)
      rw [h1, h2]
    · have ha0 : c.b (c.vec x) (c.vec y) ≠ 0 :=
        fun h0 => hcomm ((c.commute_iff x hx.1 y hy.1 hxy).mpr h0)
      have hnc' : ¬ Commute (h * x * h⁻¹) (h * y * h⁻¹) :=
        fun hc => hcomm ((Commute.conj_iff h).mp hc)
      have hb0 : c.b (c.vec (h * x * h⁻¹)) (c.vec (h * y * h⁻¹)) ≠ 0 :=
        fun h0 => hnc' ((c.commute_iff _ hx' _ hy' hne').mpr h0)
      exact sq_eq_sq_of_ne_zero _ _ ha0 hb0
        (sq_eq_one_iff_conj c hh hx hy hxy ha0 hb0)

omit [Finite G] in
private theorem conj_mul_mem_inter {v x y : G}
    (hx : x ∈ commSet D hC.d ∩ commSet D v)
    (hy : y ∈ commSet D hC.d ∩ commSet D v) :
    x * y * x⁻¹ ∈ commSet D hC.d ∩ commSet D v := by
  have hxD : x * y * x⁻¹ ∈ D := hC.setup.conj_mem x hy.1.1
  have hxdd : x⁻¹ * hC.d * x = hC.d := by
    rw [hx.1.2.1.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hxvd : x⁻¹ * v * x = v := by
    rw [hx.2.2.1.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hu_ne_d : x * y * x⁻¹ ≠ hC.d := by
    intro hu
    have hy_d : y = hC.d := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * hC.d * x := by rw [hu]
        _ = hC.d := hxdd
    exact hy.1.2.2 hy_d
  have hu_ne_v : x * y * x⁻¹ ≠ v := by
    intro hu
    have hy_v : y = v := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * v * x := by rw [hu]
        _ = v := hxvd
    exact hy.2.2.2 hy_v
  have hu_comm_d : Commute (x * y * x⁻¹) hC.d := by
    have h1 : Commute (x⁻¹ * (x * y * x⁻¹) * x) (x⁻¹ * hC.d * x) := by
      rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group, hxdd]
      exact hy.1.2.1
    have h2 := (Commute.conj_iff x⁻¹).mp (by simpa using h1)
    simpa using h2
  have hu_comm_v : Commute (x * y * x⁻¹) v := by
    have h1 : Commute (x⁻¹ * (x * y * x⁻¹) * x) (x⁻¹ * v * x) := by
      rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group, hxvd]
      exact hy.2.2.1
    have h2 := (Commute.conj_iff x⁻¹).mp (by simpa using h1)
    simpa using h2
  exact ⟨⟨hxD, hu_comm_d, hu_ne_d⟩, hxD, hu_comm_v, hu_ne_v⟩

omit [Finite G] in
private theorem conj_mul_vec_eq (c : FiveChart hC n) {v h : G}
    (hh : h * v * h⁻¹ = hC.d) {x y : G}
    (hx : x ∈ commSet D hC.d ∩ commSet D v)
    (hy : y ∈ commSet D hC.d ∩ commSet D v) :
    ∃ u ∈ commSet D hC.d ∩ commSet D v,
      (c.vec u = act (refl c.b (c.vec x)) (c.vec y) ∨
        c.vec u = -act (refl c.b (c.vec x)) (c.vec y)) ∧
      (c.vec (h * u * h⁻¹) =
          act (refl c.b (c.vec (h * x * h⁻¹))) (c.vec (h * y * h⁻¹)) ∨
        c.vec (h * u * h⁻¹) =
          -act (refl c.b (c.vec (h * x * h⁻¹))) (c.vec (h * y * h⁻¹))) := by
  have hx' : h * x * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hx.2
  have hy' : h * y * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hy.2
  refine ⟨x * y * x⁻¹, conj_mul_mem_inter hx hy, ?_, ?_⟩
  · have h := c.vec_conj x hx.1 y hy.1
    have hact := act_refl_sub (c := c) (x := x) hx.1 (c.vec y)
    rcases h with h | h
    · left; rw [h, hact]
    · right; rw [h, hact]
  · have huo : h * (x * y * x⁻¹) * h⁻¹ =
        (h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ := by group
    have hvc := c.vec_conj (h * x * h⁻¹) hx' (h * y * h⁻¹) hy'
    have hact := act_refl_sub (c := c) (x := h * x * h⁻¹) hx' (c.vec (h * y * h⁻¹))
    rw [huo]
    rcases hvc with hvc | hvc
    · left; rw [hvc, hact]
    · right; rw [hvc, hact]

omit [Finite G] in
private theorem b_proj_pivot (c : FiveChart hC n) {P Q : G}
    (hP : P ∈ commSet D hC.d) :
    c.b (c.vec Q - c.b (c.vec Q) (c.vec P) • c.vec P) (c.vec P) = 0 := by
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
    c.norm_vec P hP, mul_one]
  ring

omit [Finite G] in
private theorem b_proj_proj (c : FiveChart hC n) {P Q : G}
    (hP : P ∈ commSet D hC.d) (hQ : Q ∈ commSet D hC.d) :
    c.b (c.vec Q - c.b (c.vec Q) (c.vec P) • c.vec P)
        (c.vec Q - c.b (c.vec Q) (c.vec P) • c.vec P)
      = 1 - c.b (c.vec Q) (c.vec P) ^ 2 := by
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [c.norm_vec P hP, c.norm_vec Q hQ, mul_one, c.hsym (c.vec P) (c.vec Q)]
  ring

omit [Finite G] in
private theorem orderOf_mul_pivot_eq_if (c : FiveChart hC n) {w h : G}
    (hP : h * hC.d * h⁻¹ ∈ commSet D hC.d)
    (hQ : h * w * h⁻¹ ∈ commSet D hC.d)
    (hPQ : h * hC.d * h⁻¹ ≠ h * w * h⁻¹)
    (hnc : ¬ Commute (h * hC.d * h⁻¹) (h * w * h⁻¹)) :
    orderOf (hC.d * w) =
      if c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 = 1 then 5 else 3 := by
  have hbq : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ≠ 0 := by
    rw [c.hsym (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹))]
    intro h0
    exact hnc ((c.commute_iff _ hP _ hQ hPQ).mpr h0)
  have hb : c.b (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹)) ≠ 0 := by
    rwa [c.hsym (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹))]
  have hord := c.orderOf_mul _ hP _ hQ hPQ hb
  have hconj : orderOf (h * hC.d * h⁻¹ * (h * w * h⁻¹)) = orderOf (hC.d * w) :=
    orderOf_conj_mul h hC.d w
  have hsym : c.b (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹)) ^ 2
      = c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 := by
    rw [c.hsym (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹))]
  rw [← hconj, hord, hsym]

omit [Finite G] in
private theorem z_ne_zero (c : FiveChart hC n) {w h : G} {z : Fin n → ZMod 5}
    (hP : h * hC.d * h⁻¹ ∈ commSet D hC.d)
    (hQ : h * w * h⁻¹ ∈ commSet D hC.d)
    (hPQ : h * hC.d * h⁻¹ ≠ h * w * h⁻¹)
    (hzq : z = 0 ↔ c.vec (h * w * h⁻¹) -
      c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) • c.vec (h * hC.d * h⁻¹) = 0) :
    z ≠ 0 := by
  intro hz
  have hq0 : c.vec (h * w * h⁻¹) -
      c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) • c.vec (h * hC.d * h⁻¹) = 0 :=
    hzq.mp hz
  have hQt : c.vec (h * w * h⁻¹) =
      c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) • c.vec (h * hC.d * h⁻¹) :=
    sub_eq_zero.mp hq0
  have ht2 : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 = 1 := by
    have h1 : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * w * h⁻¹)) = 1 := c.norm_vec _ hQ
    rw [hQt, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      c.norm_vec _ hP, mul_one] at h1
    rwa [pow_two]
  rcases (by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact sq_eq_one_iff.mp ht2) with h1 | h1
  · exact hPQ (c.eq_of_vec _ hP _ hQ (Or.inl (by rw [hQt, h1, one_smul]))).symm
  · exact hPQ (c.eq_of_vec _ hP _ hQ (Or.inr (by rw [hQt, h1, neg_one_smul]))).symm

omit [Finite G] in
private theorem norm_z_if (c : FiveChart hC n) {w h : G} {z : Fin n → ZMod 5}
    (hP : h * hC.d * h⁻¹ ∈ commSet D hC.d)
    (hQ : h * w * h⁻¹ ∈ commSet D hC.d)
    (hPQ : h * hC.d * h⁻¹ ≠ h * w * h⁻¹)
    (hnc : ¬ Commute (h * hC.d * h⁻¹) (h * w * h⁻¹))
    (hordif : orderOf (hC.d * w) =
      if c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 = 1 then 5 else 3)
    (hz : c.b z z =
      1 - c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2) :
    (if orderOf (hC.d * w) = 5 then c.b z z = 0 else c.b z z = 2) := by
  have ht0 : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ≠ 0 := by
    rw [c.hsym (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹))]
    intro h0
    exact hnc ((c.commute_iff _ hP _ hQ hPQ).mpr h0)
  by_cases h5 : orderOf (hC.d * w) = 5
  · rw [if_pos h5, hz]
    have ht2 : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 = 1 := by
      have h := hordif
      rw [h5] at h
      by_contra hc
      rw [if_neg hc] at h
      exact absurd h (by decide)
    rw [ht2]
    decide
  · rw [if_neg h5, hz]
    have ht2ne : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 ≠ 1 := by
      intro ht2
      have h := hordif
      rw [if_pos ht2] at h
      exact h5 h
    have ht2 : c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) ^ 2 = 4 :=
      sq_eq_four_of_ne_zero_of_ne_one _ ht0 ht2ne
    rw [ht2]
    decide

omit [Finite G] in
private theorem commute_iff_vec_z (c : FiveChart hC n) {w v h : G} {z : Fin n → ZMod 5}
    (hwd : ¬ Commute w hC.d)
    (hh : h * v * h⁻¹ = hC.d)
    (hQ : h * w * h⁻¹ ∈ commSet D hC.d)
    (hgP : ∀ x ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) = 0)
    (hzperp : ∀ x ∈ commSet D hC.d ∩ commSet D v,
      (c.b (c.vec x) z = 0 ↔
        c.b (c.vec (h * x * h⁻¹))
          (c.vec (h * w * h⁻¹) -
            c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) •
              c.vec (h * hC.d * h⁻¹)) = 0)) :
    ∀ x ∈ commSet D hC.d ∩ commSet D v, (Commute x w ↔ c.b (c.vec x) z = 0) := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ commSet D hC.d := by simpa [hh] using conj_mem_commSet hC.setup.normal h hx.2
  have hxw : x ≠ w := by
    intro hxw
    exact hwd (by rw [← hxw]; exact hx.1.2.1)
  have hdist : h * x * h⁻¹ ≠ h * w * h⁻¹ := by
    intro hEq
    exact hxw (conj_injective (x := h) hEq)
  have hq_expand (u : Fin n → ZMod 5) :
      c.b u (c.vec (h * w * h⁻¹) -
          c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) •
            c.vec (h * hC.d * h⁻¹))
        = c.b u (c.vec (h * w * h⁻¹))
          - c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) *
            c.b u (c.vec (h * hC.d * h⁻¹)) := by
    rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
  have h1 : c.b (c.vec (h * x * h⁻¹))
        (c.vec (h * w * h⁻¹) -
          c.b (c.vec (h * w * h⁻¹)) (c.vec (h * hC.d * h⁻¹)) •
            c.vec (h * hC.d * h⁻¹)) = 0 ↔
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * w * h⁻¹)) = 0 := by
    rw [hq_expand, hgP x hx, mul_zero, sub_zero]
  have h2 : c.b (c.vec (h * x * h⁻¹)) (c.vec (h * w * h⁻¹)) = 0 ↔
      Commute (h * x * h⁻¹) (h * w * h⁻¹) :=
    (c.commute_iff (h * x * h⁻¹) hx' (h * w * h⁻¹) hQ hdist).symm
  have h3 : Commute (h * x * h⁻¹) (h * w * h⁻¹) ↔ Commute x w :=
    Commute.conj_iff h
  exact ((hzperp x hx).trans ((h1.trans h2).trans h3)).symm

omit [Finite G] in
theorem orderOf_mul_pivot (c : FiveChart hC n) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hΓ : (commSet D hC.d ∩ commSet D w).Nonempty) :
    orderOf (hC.d * w) = 3 ∨ orderOf (hC.d * w) = 5 := by
  obtain ⟨v, hv⟩ := hΓ
  obtain ⟨h, hh, hPmem, hQmem, hPQ, hnc⟩ := exists_pivot (hC := hC) hw hwd hv
  have hb : c.b (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹)) ≠ 0 := by
    intro h0
    exact hnc ((c.commute_iff _ hPmem _ hQmem hPQ).mpr h0)
  have hord := c.orderOf_mul _ hPmem _ hQmem hPQ hb
  have hconj : orderOf (h * hC.d * h⁻¹ * (h * w * h⁻¹)) = orderOf (hC.d * w) :=
    orderOf_conj_mul h hC.d w
  by_cases hsq : c.b (c.vec (h * hC.d * h⁻¹)) (c.vec (h * w * h⁻¹)) ^ 2 = 1
  · right
    rw [← hconj, hord, if_pos hsq]
  · left
    rw [← hconj, hord, if_neg hsq]

omit [Finite G] in
theorem exists_local_hyperplane (c : FiveChart hC n) (hn : 5 ≤ n) {w v : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hv : v ∈ commSet D hC.d ∩ commSet D w) :
    ∃ z, z ≠ 0 ∧ c.b z (c.vec v) = 0 ∧
      (if orderOf (hC.d * w) = 5 then c.b z z = 0 else c.b z z = 2) ∧
      ∀ x ∈ commSet D hC.d ∩ commSet D v, (Commute x w ↔ c.b (c.vec x) z = 0) := by
  obtain ⟨h, hh, hP, hQ, hPQ, hnc⟩ := exists_pivot (hC := hC) hw hwd hv
  set P : G := h * hC.d * h⁻¹ with hPdef
  set Q : G := h * w * h⁻¹ with hQdef
  set t : ZMod 5 := c.b (c.vec Q) (c.vec P) with ht
  set q : Fin n → ZMod 5 := c.vec Q - t • c.vec P with hqdef
  have hqP : c.b q (c.vec P) = 0 := b_proj_pivot c hP
  have hq_norm : c.b q q = 1 - t ^ 2 := b_proj_proj c hP hQ
  have hf : ∀ x ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec x) (c.vec x) = 1 ∧ c.b (c.vec x) (c.vec v) = 0 :=
    vec_norm_perp_pivot c hv.1
  have hg : ∀ x ∈ commSet D hC.d ∩ commSet D v,
      c.b (c.vec (h * x * h⁻¹)) (c.vec (h * x * h⁻¹)) = 1 ∧
      c.b (c.vec (h * x * h⁻¹)) (c.vec P) = 0 :=
    vec_conj_norm_perp_pivot c hh hP
  obtain ⟨z, hzv, hzz, hzq, hzperp⟩ :=
    FiveRigid.exists_perp_iff_of_reflClosed c.hsym c.hnd hn (c.norm_vec v hv.1)
      (c.norm_vec P hP)
      (S := commSet D hC.d ∩ commSet D v) (f := c.vec)
      (g := fun x => c.vec (h * x * h⁻¹)) hf hg
      (exists_mem_inter_vec c hv.1) (sq_vec_conj_eq c hh)
      (fun x hx y hy => conj_mul_vec_eq c hh hx hy)
      (q := q) hqP
  have hz_norm : c.b z z = 1 - t ^ 2 := hzz.trans hq_norm
  have hordif := orderOf_mul_pivot_eq_if c hP hQ hPQ hnc
  refine ⟨z, z_ne_zero c hP hQ hPQ hzq, hzv,
    norm_z_if c hP hQ hPQ hnc hordif hz_norm, ?_⟩
  exact commute_iff_vec_z c hwd hh hQ (fun x hx => (hg x hx).2) hzperp

end FiveChart

end CFSG.OddTranspositions.PartThree
