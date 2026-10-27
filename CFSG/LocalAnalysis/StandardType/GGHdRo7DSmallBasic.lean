module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmBasicAux_sq_of_ne_zero {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := by
  revert x
  decide

private lemma hdRo7DSmBasicAux_eq_one_or_neg_one {x : ZMod 3} (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  revert x
  decide

private lemma hdRo7DSmBasicAux_two_eq_neg_one : (2 : ZMod 3) = -1 := by decide

private lemma hdRo7DSmBasicAux_four_eq_one : (4 : ZMod 3) = 1 := by decide

private lemma hdRo7DSmBasicAux_add_self {n : ℕ} (h : DV n) : h + h = -h := by
  rw [← two_smul (ZMod 3) h, hdRo7DSmBasicAux_two_eq_neg_one, neg_one_smul]

private lemma hdRo7DSmBasicAux_dB_add_left {n : ℕ} (ρ : ZMod 3) (x y z : DV n) :
    dB ρ (x + y) z = dB ρ x z + dB ρ y z := by
  simp only [dB, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma hdRo7DSmBasicAux_dB_smul_left {n : ℕ} (ρ : ZMod 3) (a : ZMod 3) (x z : DV n) :
    dB ρ (a • x) z = a * dB ρ x z := by
  simp only [dB, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  exact congr_arg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun i _ => by ring)

private lemma hdRo7DSmBasicAux_dB_neg_left {n : ℕ} (ρ : ZMod 3) (x z : DV n) :
    dB ρ (-x) z = -dB ρ x z := by
  simpa using hdRo7DSmBasicAux_dB_smul_left ρ (-1) x z

private lemma hdRo7DSmBasicAux_dB_add_right {n : ℕ} (ρ : ZMod 3) (x y z : DV n) :
    dB ρ x (y + z) = dB ρ x y + dB ρ x z := by
  simp only [dB, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private lemma hdRo7DSmBasicAux_dB_smul_right {n : ℕ} (ρ : ZMod 3) (a : ZMod 3) (x z : DV n) :
    dB ρ x (a • z) = a * dB ρ x z := by
  simp only [dB, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  exact congr_arg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun i _ => by ring)

private lemma hdRo7DSmBasicAux_dB_neg_right {n : ℕ} (ρ : ZMod 3) (x z : DV n) :
    dB ρ x (-z) = -dB ρ x z := by
  simpa using hdRo7DSmBasicAux_dB_smul_right ρ (-1) x z

private lemma hdRo7DSmBasicAux_dB_sub_left {n : ℕ} (ρ : ZMod 3) (x y z : DV n) :
    dB ρ (x - y) z = dB ρ x z - dB ρ y z := by
  rw [sub_eq_add_neg, hdRo7DSmBasicAux_dB_add_left, hdRo7DSmBasicAux_dB_neg_left]
  ring

private lemma hdRo7DSmBasicAux_dB_sub_right {n : ℕ} (ρ : ZMod 3) (x y z : DV n) :
    dB ρ x (y - z) = dB ρ x y - dB ρ x z := by
  rw [sub_eq_add_neg, hdRo7DSmBasicAux_dB_add_right, hdRo7DSmBasicAux_dB_neg_right]
  ring

private lemma hdRo7DSmBasicAux_dB_neg_neg {n : ℕ} (ρ : ZMod 3) (h : DV n) :
    dB ρ (-h) (-h) = dB ρ h h := by
  rw [hdRo7DSmBasicAux_dB_neg_left, hdRo7DSmBasicAux_dB_neg_right, neg_neg]

private lemma hdRo7DSmBasicAux_dB_zero {n : ℕ} (ρ : ZMod 3) :
    dB ρ (0 : DV n) (0 : DV n) = 0 := by
  simp [dB]

theorem dB_comm {n : ℕ} (ρ : ZMod 3) (x y : DV n) : dB ρ x y = dB ρ y x := by
  simp only [dB]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

@[expose] noncomputable def dFun {n : ℕ} (ρ : ZMod 3) (h : DV n) : Module.Dual (ZMod 3) (DV n) where
  toFun v := 2 * dB ρ h h * dB ρ h v
  map_add' x y := by
    simp only [dB, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [dB, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hs : ∑ i : Fin n, h i.succ * (c * x i.succ) = c * ∑ i : Fin n, h i.succ * x i.succ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    ring

theorem dFun_apply {n : ℕ} (ρ : ZMod 3) (h v : DV n) : dFun ρ h v = 2 * dB ρ h h * dB ρ h v :=
  rfl

theorem dFun_self {n : ℕ} {ρ : ZMod 3} {h : DV n} (hh : dB ρ h h ≠ 0) : dFun ρ h h = 2 := by
  rw [dFun_apply]
  have hQ : dB ρ h h * dB ρ h h = 1 := hdRo7DSmBasicAux_sq_of_ne_zero hh
  calc
    2 * dB ρ h h * dB ρ h h = 2 * (dB ρ h h * dB ρ h h) := by ring
    _ = 2 * 1 := by rw [hQ]
    _ = 2 := by ring

theorem dRefl_apply {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n} (hr : DRefl ρ r h) (v : DV n) :
    r v = v - dFun ρ h v • h := by
  rw [hr.2 v, dFun_apply]
  rfl

private lemma hdRo7DSmBasicAux_dRef_involutive {n : ℕ} {ρ : ZMod 3} {h : DV n}
    (hh : dB ρ h h ≠ 0) : Function.Involutive (dRef ρ h) := by
  have hfun : dRef ρ h = ⇑(Module.reflection (dFun_self hh)) := by
    funext v
    rw [Module.reflection_apply, dFun_apply]
    rfl
  intro v
  rw [hfun]
  exact Module.involutive_reflection (dFun_self hh) v

private lemma hdRo7DSmBasicAux_dRef_dRef {n : ℕ} {ρ : ZMod 3} {h : DV n}
    (hh : dB ρ h h ≠ 0) (g : DV n) : dRef ρ h (dRef ρ h g) = g :=
  hdRo7DSmBasicAux_dRef_involutive hh g

private lemma hdRo7DSmBasicAux_dB_dRef_sub {n : ℕ} (ρ : ZMod 3) {h : DV n} (a b : ZMod 3)
    (x y : DV n) :
    dB ρ (x - a • h) (y - b • h) =
      dB ρ x y - b * dB ρ x h - a * dB ρ h y + a * b * dB ρ h h := by
  rw [hdRo7DSmBasicAux_dB_sub_left, hdRo7DSmBasicAux_dB_sub_right,
    hdRo7DSmBasicAux_dB_sub_right, hdRo7DSmBasicAux_dB_smul_right,
    hdRo7DSmBasicAux_dB_smul_left, hdRo7DSmBasicAux_dB_smul_left,
    hdRo7DSmBasicAux_dB_smul_right]
  ring

private lemma hdRo7DSmBasicAux_cross (Q Bx By : ZMod 3) (hQ : Q * Q = 1) :
    (2 * Q * Bx) * (2 * Q * By) * Q = (2 * Q * By) * Bx + (2 * Q * Bx) * By := by
  have h4 : (4 : ZMod 3) = 1 := hdRo7DSmBasicAux_four_eq_one
  calc
    (2 * Q * Bx) * (2 * Q * By) * Q = 4 * (Q * Q) * Q * (Bx * By) := by ring
    _ = 4 * Q * (Bx * By) := by rw [hQ]; ring
    _ = Q * (Bx * By) := by rw [h4]; ring
    _ = (2 * Q * By) * Bx + (2 * Q * Bx) * By := by
      rw [show Q * (Bx * By) = 4 * Q * (Bx * By) by rw [h4]; ring]
      ring

theorem dB_dRef {n : ℕ} {ρ : ZMod 3} {h : DV n} (hh : dB ρ h h ≠ 0) (x y : DV n) :
    dB ρ (dRef ρ h x) (dRef ρ h y) = dB ρ x y := by
  have hQ : dB ρ h h * dB ρ h h = 1 := hdRo7DSmBasicAux_sq_of_ne_zero hh
  have hkey := hdRo7DSmBasicAux_cross (dB ρ h h) (dB ρ h x) (dB ρ h y) hQ
  simp only [dRef]
  rw [hdRo7DSmBasicAux_dB_dRef_sub, dB_comm ρ x h]
  rw [hkey]
  ring

private lemma hdRo7DSmBasicAux_dB_dRef_cross {n : ℕ} {ρ : ZMod 3} {h : DV n}
    (hh : dB ρ h h ≠ 0) (g v : DV n) :
    dB ρ (dRef ρ h g) v = dB ρ g (dRef ρ h v) := by
  conv_lhs => rw [← hdRo7DSmBasicAux_dRef_dRef hh v]
  exact dB_dRef hh g (dRef ρ h v)

private lemma hdRo7DSmBasicAux_dRef_neg {n : ℕ} (ρ : ZMod 3) (h v : DV n) :
    dRef ρ (-h) v = dRef ρ h v := by
  have h1 : dB ρ (-h) (-h) = dB ρ h h := hdRo7DSmBasicAux_dB_neg_neg ρ h
  have h2 : dB ρ (-h) v = -dB ρ h v := hdRo7DSmBasicAux_dB_neg_left ρ h v
  rw [dRef, dRef, h1, h2]
  rw [show 2 * dB ρ h h * (-dB ρ h v) = -(2 * dB ρ h h * dB ρ h v) by ring]
  rw [neg_smul, smul_neg, neg_neg]

theorem exists_dRefl {n : ℕ} {ρ : ZMod 3} {h : DV n} (hh : dB ρ h h ≠ 0) :
    ∃ r : DGL n, DRefl ρ r h := by
  refine ⟨Module.reflection (dFun_self hh), hh, fun v => ?_⟩
  rw [Module.reflection_apply, dFun_apply]
  rfl

theorem dRefl_unique {n : ℕ} {ρ : ZMod 3} {r r' : DGL n} {h : DV n} (hr : DRefl ρ r h)
    (hr' : DRefl ρ r' h) : r = r' := by
  apply LinearEquiv.ext
  intro v
  rw [hr.2 v, hr'.2 v]

theorem dRefl_neg_iff {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n} :
    DRefl ρ r (-h) ↔ DRefl ρ r h := by
  constructor
  · rintro ⟨hh, hv⟩
    exact ⟨by rwa [← hdRo7DSmBasicAux_dB_neg_neg ρ h], fun v => by
      rw [← hdRo7DSmBasicAux_dRef_neg ρ h v, hv v]⟩
  · rintro ⟨hh, hv⟩
    exact ⟨by rwa [hdRo7DSmBasicAux_dB_neg_neg ρ h], fun v => by
      rw [hdRo7DSmBasicAux_dRef_neg ρ h v, hv v]⟩

private lemma hdRo7DSmBasicAux_sq {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    (hr : DRefl ρ r h) : r * r = 1 := by
  have hrefl : r = Module.reflection (dFun_self hr.1) := LinearEquiv.ext fun v => by
    rw [dRefl_apply hr v, Module.reflection_apply, dFun_apply]
  rw [hrefl]
  nth_rewrite 2 [← Module.reflection_inv (dFun_self hr.1)]
  exact mul_inv_cancel _

private lemma hdRo7DSmBasicAux_inv {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    (hr : DRefl ρ r h) : r⁻¹ = r := by
  have hrr : r * r = 1 := hdRo7DSmBasicAux_sq hr
  calc
    r⁻¹ = r⁻¹ * 1 := (mul_one r⁻¹).symm
    _ = r⁻¹ * (r * r) := by rw [hrr]
    _ = (r⁻¹ * r) * r := by group
    _ = 1 * r := by rw [inv_mul_cancel]
    _ = r := one_mul r

private lemma hdRo7DSmBasicAux_apply_sq {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    (hr : DRefl ρ r h) (v : DV n) : r (r v) = v := by
  have h := congrArg (fun e : DGL n => e v) (hdRo7DSmBasicAux_sq hr)
  simpa [LinearEquiv.mul_apply] using h

private lemma hdRo7DSmBasicAux_h_ne_zero {n : ℕ} {ρ : ZMod 3} {h : DV n}
    (hh : dB ρ h h ≠ 0) : h ≠ 0 := by
  intro h0
  exact hh (by rw [h0, hdRo7DSmBasicAux_dB_zero])

private lemma hdRo7DSmBasicAux_move_apply {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    (hr : DRefl ρ r h) (v : DV n) :
    (r.toLinearMap - (LinearMap.id : DV n →ₗ[ZMod 3] DV n)) v = -dFun ρ h v • h := by
  rw [LinearMap.sub_apply, LinearMap.id_apply]
  change r v - v = -dFun ρ h v • h
  rw [dRefl_apply hr v]
  module

theorem ggLinMove_of_dRefl {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n} (hr : DRefl ρ r h) :
    ggLinMove r = Submodule.span (ZMod 3) {h} := by
  rw [ggLinMove]
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    rw [hdRo7DSmBasicAux_move_apply hr v]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton h))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨h, ?_⟩
    rw [hdRo7DSmBasicAux_move_apply hr h, dFun_self hr.1,
      hdRo7DSmBasicAux_two_eq_neg_one]
    module

theorem ggLinRefl_of_dRefl {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n} (hr : DRefl ρ r h) :
    GGLinRefl r := by
  refine ⟨hdRo7DSmBasicAux_sq hr, ?_⟩
  rw [ggLinMove_of_dRefl hr, finrank_span_singleton (hdRo7DSmBasicAux_h_ne_zero hr.1)]

theorem dRefl_root_unique {n : ℕ} {ρ ρ' : ZMod 3} {r : DGL n} {h h' : DV n} (hr : DRefl ρ r h)
    (hr' : DRefl ρ' r h') : h' = h ∨ h' = -h := by
  have hspan : ggLinMove r = Submodule.span (ZMod 3) {h} := ggLinMove_of_dRefl hr
  have hspan' : ggLinMove r = Submodule.span (ZMod 3) {h'} := ggLinMove_of_dRefl hr'
  have hmem : h' ∈ Submodule.span (ZMod 3) {h} := by
    rw [← hspan, hspan']
    exact Submodule.subset_span (Set.mem_singleton h')
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hh'ne : h' ≠ 0 := hdRo7DSmBasicAux_h_ne_zero hr'.1
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hh'ne hc.symm
  rcases hdRo7DSmBasicAux_eq_one_or_neg_one hcne with h1 | h1
  · left
    rw [← hc, h1, one_smul]
  · right
    rw [← hc, h1, neg_one_smul]

theorem dRefl_of_isometry {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ : φ h = 2) (hr : ∀ v, r v = v - φ v • h)
    (hiso : ∀ x y, dB ρ (r x) (r y) = dB ρ x y) (hh : dB ρ h h ≠ 0) : DRefl ρ r h := by
  have hrh : r h = -h := by
    calc
      r h = h - φ h • h := hr h
      _ = h - (2 : ZMod 3) • h := by rw [hφ]
      _ = h - (-h) := by rw [hdRo7DSmBasicAux_two_eq_neg_one, neg_one_smul]
      _ = h + h := sub_neg_eq_add h h
      _ = -h := hdRo7DSmBasicAux_add_self h
  have hkey : ∀ x, φ x * dB ρ h h = 2 * dB ρ h x := by
    intro x
    have his := hiso x h
    rw [hrh, hr x, hdRo7DSmBasicAux_dB_sub_left, hdRo7DSmBasicAux_dB_neg_right,
      hdRo7DSmBasicAux_dB_smul_left, hdRo7DSmBasicAux_dB_neg_right] at his
    rw [dB_comm ρ x h] at his
    linear_combination his
  refine ⟨hh, fun v => ?_⟩
  have hQ : dB ρ h h * dB ρ h h = 1 := hdRo7DSmBasicAux_sq_of_ne_zero hh
  have hphi : φ v = 2 * dB ρ h h * dB ρ h v := by
    calc
      φ v = φ v * (dB ρ h h * dB ρ h h) := by rw [hQ, mul_one]
      _ = (φ v * dB ρ h h) * dB ρ h h := by ring
      _ = (2 * dB ρ h v) * dB ρ h h := by rw [hkey v]
      _ = 2 * dB ρ h h * dB ρ h v := by ring
  rw [hr v, dRef, hphi]

theorem dRefl_conj {n : ℕ} {ρ : ZMod 3} {r s : DGL n} {h g : DV n} (hr : DRefl ρ r h)
    (hs : DRefl ρ s g) : DRefl ρ (r * s * r⁻¹) (dRef ρ h g) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [dB_dRef hr.1]
    exact hs.1
  · have hrrv : r (r v) = v := hdRo7DSmBasicAux_apply_sq hr v
    have hr2 : r⁻¹ = r := hdRo7DSmBasicAux_inv hr
    have hB : dB ρ g (r v) = dB ρ (dRef ρ h g) v := by
      rw [hr.2 v]
      exact (hdRo7DSmBasicAux_dB_dRef_cross hr.1 g v).symm
    calc
      (r * s * r⁻¹) v = r (s (r v)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr2]
      _ = r (r v - (2 * dB ρ g g * dB ρ g (r v)) • g) := by
        rw [dRefl_apply hs (r v), dFun_apply]
      _ = r (r v) - (2 * dB ρ g g * dB ρ g (r v)) • r g := by
        rw [map_sub, map_smul]
      _ = v - (2 * dB ρ g g * dB ρ (dRef ρ h g) v) • dRef ρ h g := by
        rw [hrrv, hr.2 g, hB]
      _ = dRef ρ (dRef ρ h g) v := by
        conv_rhs => rw [dRef]
        rw [dB_dRef hr.1 g g]

theorem dB_dAct {n : ℕ} (ρ : ZMod 3) {σ : Equiv.Perm (Fin (n + 1))} {c : Fin (n + 1) → ZMod 3}
    (hσ : σ 0 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) (x y : DV n) :
    dB ρ (dAct σ c x) (dAct σ c y) = dB ρ x y := by
  have hσ' : σ.symm 0 = 0 := by simpa using (congrArg σ.symm hσ).symm
  have hc0 : c 0 * c 0 = 1 := by
    rcases hc 0 with h | h <;> rw [h] <;> ring
  have hf0 : dAct σ c x 0 * dAct σ c y 0 = x 0 * y 0 := by
    rw [show dAct σ c x 0 = c 0 * x 0 by simp [dAct, hσ'],
      show dAct σ c y 0 = c 0 * y 0 by simp [dAct, hσ']]
    rw [show (c 0 * x 0) * (c 0 * y 0) = (c 0 * c 0) * (x 0 * y 0) by ring, hc0,
      one_mul]
  have hsum : ∑ j : Fin (n + 1), (dAct σ c x j) * (dAct σ c y j) =
      ∑ i : Fin (n + 1), x i * y i := by
    calc
      ∑ j : Fin (n + 1), (dAct σ c x j) * (dAct σ c y j) =
          ∑ j : Fin (n + 1), (c (σ.symm j) * c (σ.symm j)) *
            (x (σ.symm j) * y (σ.symm j)) := by
        exact Finset.sum_congr rfl fun j _ => by simp [dAct]; ring
      _ = ∑ i : Fin (n + 1), (c i * c i) * (x i * y i) := by
        simpa using (Equiv.sum_comp σ.symm (fun i : Fin (n + 1) =>
          (c i * c i) * (x i * y i)))
      _ = ∑ i : Fin (n + 1), x i * y i := by
        exact Finset.sum_congr rfl fun i _ => by
          have hci : c i * c i = 1 := by
            rcases hc i with h | h <;> rw [h] <;> ring
          rw [hci, one_mul]
  have hbn : ∑ i : Fin n, (dAct σ c x i.succ) * (dAct σ c y i.succ) =
      (∑ j : Fin (n + 1), x j * y j) - x 0 * y 0 := by
    calc
      ∑ i : Fin n, (dAct σ c x i.succ) * (dAct σ c y i.succ) =
          ((dAct σ c x 0) * (dAct σ c y 0) +
            ∑ i : Fin n, (dAct σ c x i.succ) * (dAct σ c y i.succ)) -
            (dAct σ c x 0) * (dAct σ c y 0) := by abel
      _ = (∑ j : Fin (n + 1), (dAct σ c x j) * (dAct σ c y j)) -
            (dAct σ c x 0) * (dAct σ c y 0) := by
        rw [Fin.sum_univ_succ]
      _ = (∑ j : Fin (n + 1), x j * y j) - x 0 * y 0 := by rw [hsum, hf0]
  have hbn' : ∑ i : Fin n, x i.succ * y i.succ =
      (∑ j : Fin (n + 1), x j * y j) - x 0 * y 0 := by
    calc
      ∑ i : Fin n, x i.succ * y i.succ =
          (x 0 * y 0 + ∑ i : Fin n, x i.succ * y i.succ) - x 0 * y 0 := by abel
      _ = (∑ j : Fin (n + 1), x j * y j) - x 0 * y 0 := by
        rw [Fin.sum_univ_succ]
  simp only [dB]
  rw [hbn, hbn']
  rw [show ρ * dAct σ c x 0 * dAct σ c y 0 = ρ * (dAct σ c x 0 * dAct σ c y 0) by ring,
    hf0]
  ring

private lemma hdRo7DSmBasicAux_dAct_dE {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (i : Fin (n + 1)) :
    dAct σ c (dE n i) = c i • dE n (σ i) := by
  funext j
  rw [dAct, dE, dE, Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : j = σ i
  · subst h
    simp
  · have h' : σ.symm j ≠ i := fun hh => h (by rw [← hh, Equiv.apply_symm_apply])
    simp [h, h']

private lemma hdRo7DSmBasicAux_dStd_eq_dE {n : ℕ} (i : Fin (n + 1)) :
    dStd n i = dE n i := by
  rw [dStd, Pi.basisFun_apply]
  rfl

private lemma hdRo7DSmBasicAux_dActL_basis {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1) → ZMod 3} (hc : ∀ i, c i = 1 ∨ c i = -1) (i : Fin (n + 1)) :
    dActL σ c hc (dStd n i) = c i • dStd n (σ i) := by
  rw [dActL_apply, hdRo7DSmBasicAux_dStd_eq_dE i, hdRo7DSmBasicAux_dAct_dE,
    ← hdRo7DSmBasicAux_dStd_eq_dE (σ i)]

theorem dB_of_c2sp {n : ℕ} {a : DGL n} (ha : C2SP 3 (dStd n) a) (ρ : ZMod 3) (x y : DV n) :
    dB ρ (a x) (a y) = dB ρ x y := by
  obtain ⟨σ, c, hσ, hc0, hc, hact⟩ := ha
  have haeq : a = dActL σ c hc := by
    apply LinearEquiv.ext
    intro v
    have hlin : (a : DV n →ₗ[ZMod 3] DV n) =
        ((dActL σ c hc : DGL n) : DV n →ₗ[ZMod 3] DV n) := by
      apply Module.Basis.ext (dStd n)
      intro i
      change a (dStd n i) = dActL σ c hc (dStd n i)
      rw [hact i, hdRo7DSmBasicAux_dActL_basis hc i]
    exact congrArg (fun f : DV n →ₗ[ZMod 3] DV n => f v) hlin
  rw [haeq]
  simpa only [dActL_apply] using dB_dAct ρ hσ hc x y

private lemma hdRo7DSmBasicAux_dRef_map {n : ℕ} {ρ : ZMod 3} {h : DV n}
    {w : DGL n} (hw : ∀ x y, dB ρ (w x) (w y) = dB ρ x y)
    (u : DV n) : w (dRef ρ h u) = dRef ρ (w h) (w u) := by
  have hQ : dB ρ (w h) (w h) = dB ρ h h := hw h h
  have hB : dB ρ (w h) (w u) = dB ρ h u := hw h u
  rw [dRef, dRef, hQ, hB, map_sub, map_smul]

theorem dRefl_conj_dActL {n : ℕ} {ρ : ZMod 3} {σ : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1) → ZMod 3} (hσ : σ 0 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) {r : DGL n}
    {h : DV n} (hr : DRefl ρ r h) :
    DRefl ρ (dActL σ c hc * r * (dActL σ c hc)⁻¹) (dAct σ c h) := by
  have hw : ∀ x y, dB ρ (dActL σ c hc x) (dActL σ c hc y) = dB ρ x y := by
    intro x y
    simpa only [dActL_apply] using dB_dAct ρ hσ hc x y
  refine ⟨?_, fun v => ?_⟩
  · rw [dB_dAct ρ hσ hc h h]
    exact hr.1
  · have hww : dActL σ c hc ((dActL σ c hc)⁻¹ v) = v := by
      simp
    calc
      (dActL σ c hc * r * (dActL σ c hc)⁻¹) v =
          dActL σ c hc (r ((dActL σ c hc)⁻¹ v)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = dActL σ c hc (dRef ρ h ((dActL σ c hc)⁻¹ v)) := by rw [hr.2 _]
      _ = dRef ρ (dActL σ c hc h) (dActL σ c hc ((dActL σ c hc)⁻¹ v)) :=
        hdRo7DSmBasicAux_dRef_map hw ((dActL σ c hc)⁻¹ v)
      _ = dRef ρ (dAct σ c h) v := by rw [hww, dActL_apply]

theorem dsp_dActL {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {c : Fin (n + 1) → ZMod 3}
    (hd : DSPData σ c) : DSP 3 (dStd n) (dActL σ c hd.2.2.1) := by
  refine ⟨σ, c, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, fun i => ?_⟩
  exact hdRo7DSmBasicAux_dActL_basis hd.2.2.1 i

private lemma hdRo7DSmBasicAux_dB_dE_of_zero {n : ℕ} (ρ : ZMod 3) {h : DV n}
    (h0 : h 0 = 0) (k : Fin (n + 1)) : dB ρ h (dE n k) = h k := by
  rw [dB, dE]
  by_cases hk : k = 0
  · subst hk
    simp [h0, Fin.succ_ne_zero]
  · obtain ⟨k', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk
    rw [Finset.sum_eq_single k']
    · simp [h0]
    · intro b _ hb
      rw [Pi.single_eq_of_ne]
      · ring
      · exact fun hh => hb (Fin.succ_injective _ hh)
    · intro hk'
      exact absurd (Finset.mem_univ k') hk'

private lemma hdRo7DSmBasicAux_dRef_dE {n : ℕ} (ρ : ZMod 3) {h : DV n}
    (h0 : h 0 = 0) (hQ : dB ρ h h = 2) (k : Fin (n + 1)) :
    dRef ρ h (dE n k) = dE n k - h k • h := by
  rw [dRef, hdRo7DSmBasicAux_dB_dE_of_zero ρ h0 k, hQ]
  rw [show (2 : ZMod 3) * 2 * h k = h k by
    rw [show (2 : ZMod 3) * 2 = 1 by decide, one_mul]]

theorem dsp_of_dRefl_int {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n} (hr : DRefl ρ r h)
    (h0 : h 0 = 0) (hD : dIsD h) : DSP 3 (dStd n) r := by
  obtain ⟨i, j, hij, hi, hj, hrest⟩ := hD
  have hi0 : i ≠ 0 := by rintro hz; rw [hz] at hi; exact hi h0
  have hj0 : j ≠ 0 := by rintro hz; rw [hz] at hj; exact hj h0
  have hsupp : dSupp h = 2 := by
    rcases (dIsD_iff h).mp ⟨i, j, hij, hi, hj, hrest⟩ with ⟨-, hs⟩ | ⟨hne, -⟩
    · exact hs
    · exact absurd h0 hne
  have hQ : dB ρ h h = 2 := by rw [dB_self_of_eq ρ h0, hsupp]; norm_num
  have hrepr : h = h i • dE n i + h j • dE n j := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dE, Pi.single_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · have hk : h k = 0 := hrest k hki hkj
        simp [hki, hkj, hk]
  let q : ZMod 3 := -(h i * h j)
  have hq : q = 1 ∨ q = -1 := by
    rcases hdRo7DSmBasicAux_eq_one_or_neg_one hi with h | h <;>
      rcases hdRo7DSmBasicAux_eq_one_or_neg_one hj with h' | h' <;>
      dsimp only [q] <;> rw [h, h'] <;> norm_num
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i j
  let c : Fin (n + 1) → ZMod 3 := fun k => if k = i ∨ k = j then q else 1
  have hσ0 : σ 0 = 0 := by
    dsimp only [σ]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hj0)
  have hc0 : c 0 = 1 := by
    dsimp only [c]
    simp [Ne.symm hi0, Ne.symm hj0]
  have hc : ∀ k, c k = 1 ∨ c k = -1 := by
    intro k
    by_cases hki : k = i
    · have hck : c k = q := by
        dsimp only [c]
        rw [if_pos (Or.inl hki)]
      rcases hq with h | h
      · left; rw [hck, h]
      · right; rw [hck, h]
    · by_cases hkj : k = j
      · have hck : c k = q := by
          dsimp only [c]
          rw [if_pos (Or.inr hkj)]
        rcases hq with h | h
        · left; rw [hck, h]
        · right; rw [hck, h]
      · left
        dsimp only [c]
        rw [if_neg (not_or.mpr ⟨hki, hkj⟩)]
  have hprod : ∏ k, c k = 1 := by
    have hsuppc : ∀ x, x ∉ ({i, j} : Finset (Fin (n + 1))) → c x = 1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      dsimp only [c]
      rw [if_neg (not_or.mpr ⟨hx.1, hx.2⟩)]
    have hprod' : (∏ k, c k) = c i * c j := by
      rw [← Finset.prod_subset (s₁ := ({i, j} : Finset (Fin (n + 1))))
        (s₂ := Finset.univ) (by simp) (fun x _ hx => hsuppc x hx)]
      rw [Finset.prod_pair hij]
    rw [hprod']
    dsimp only [c]
    rw [if_pos (Or.inl rfl : i = i ∨ i = j), if_pos (Or.inr rfl : j = i ∨ j = j)]
    rcases hq with h | h <;> rw [h] <;> norm_num
  refine ⟨σ, c, hσ0, hc0, hc, hprod, fun k => ?_⟩
  rw [hdRo7DSmBasicAux_dStd_eq_dE k, hr.2, hdRo7DSmBasicAux_dRef_dE ρ h0 hQ]
  have hi_e : h i • h = h i • (h i • dE n i + h j • dE n j) :=
    congrArg (fun x => h i • x) hrepr
  have hj_e : h j • h = h j • (h i • dE n i + h j • dE n j) :=
    congrArg (fun x => h j • x) hrepr
  by_cases hki : k = i
  · subst k
    have ha2 : h i * h i = 1 := hdRo7DSmBasicAux_sq_of_ne_zero hi
    rw [hi_e, show σ i = j from Equiv.swap_apply_left i j,
      show c i = q from by dsimp only [c]; rw [if_pos (Or.inl rfl)]]
    have hexp : dE n i - h i • (h i • dE n i + h j • dE n j) =
        (1 - h i * h i) • dE n i - (h i * h j) • dE n j := by module
    rw [hexp, show 1 - h i * h i = 0 by rw [ha2]; ring, zero_smul, zero_sub,
      hdRo7DSmBasicAux_dStd_eq_dE j, neg_smul]
  · by_cases hkj : k = j
    · subst k
      have hb2 : h j * h j = 1 := hdRo7DSmBasicAux_sq_of_ne_zero hj
      rw [hj_e, show σ j = i from Equiv.swap_apply_right i j,
        show c j = q from by dsimp only [c]; rw [if_pos (Or.inr rfl)]]
      have hexp : dE n j - h j • (h i • dE n i + h j • dE n j) =
          (1 - h j * h j) • dE n j - (h j * h i) • dE n i := by module
      rw [hexp, show 1 - h j * h j = 0 by rw [hb2]; ring, zero_smul, zero_sub,
        hdRo7DSmBasicAux_dStd_eq_dE i]
      rw [show h j * h i = h i * h j by ring, neg_smul]
    · have hk : h k = 0 := hrest k hki hkj
      rw [show h k • h = 0 by rw [hk, zero_smul],
        show σ k = k from Equiv.swap_apply_of_ne_of_ne hki hkj,
        show c k = 1 from by dsimp only [c]; rw [if_neg (not_or.mpr ⟨hki, hkj⟩)]]
      rw [sub_zero, one_smul, hdRo7DSmBasicAux_dStd_eq_dE k]

private lemma hdRo7DSmBasicAux_ggLinConj_eq_mul {n : ℕ} (w r : DGL n) :
    ggLinConj w r = w * r * w⁻¹ := by
  ext v
  rfl

theorem linWeyl_dGroup_dAct {n : ℕ} {ρ : ZMod 3} {σ : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1) → ZMod 3} (hσ : σ 0 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) {Φ Ψ : Set (DV n)}
    (hΨ : ∀ h, h ∈ Ψ ↔ ∃ g ∈ Φ, dAct σ c g = h) (hW : ZS.LinWeyl 3 (dGroup ρ Φ)) :
    ZS.LinWeyl 3 (dGroup ρ Ψ) := by
  let w : DGL n := dActL σ c hc
  have hw : ∀ x y, dB ρ (w x) (w y) = dB ρ x y := by
    intro x y
    simpa only [w, dActL_apply] using dB_dAct ρ hσ hc x y
  have hconj : ∀ (r : DGL n) (g : DV n), DRefl ρ r g →
      DRefl ρ (ggLinConj w r) (dAct σ c g) := by
    intro r g hrg
    have h := dRefl_conj_dActL (ρ := ρ) hσ hc hrg
    rw [hdRo7DSmBasicAux_ggLinConj_eq_mul]
    simpa only [w] using h
  have hmap : (dGroup ρ Φ).map (ggLinConj w).toMonoidHom = dGroup ρ Ψ := by
    rw [dGroup, dGroup, MonoidHom.map_closure]
    congr 1
    ext r
    constructor
    · rintro ⟨r0, ⟨g, hg, hrg⟩, rfl⟩
      exact ⟨dAct σ c g, (hΨ _).mpr ⟨g, hg, rfl⟩, hconj r0 g hrg⟩
    · rintro ⟨h, hh, hrh⟩
      rw [hΨ] at hh
      obtain ⟨g, hg, rfl⟩ := hh
      have hgg : dB ρ g g ≠ 0 := by
        intro hzero
        have hwg : dB ρ (dAct σ c g) (dAct σ c g) = dB ρ g g := by
          simpa only [w, dActL_apply] using hw g g
        rw [hzero] at hwg
        exact hrh.1 hwg
      obtain ⟨r0, hr0⟩ := exists_dRefl (ρ := ρ) hgg
      exact ⟨r0, ⟨g, hg, hr0⟩, dRefl_unique (hconj r0 g hr0) hrh⟩
  have hW' : ZS.LinWeyl 3 ((dGroup ρ Φ).map (ggLinConj w).toMonoidHom) :=
    CFSG.StandardType.HdRo7SU.Small.linWeyl_map_ggLinConj w (dGroup ρ Φ) hW
  rwa [hmap] at hW'

end CFSG.StandardType.HdRo7D.Small
