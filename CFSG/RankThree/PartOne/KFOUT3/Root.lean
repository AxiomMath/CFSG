module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix

abbrev SL3 (K : Type) [Field K] : Type := Matrix.SpecialLinearGroup (Fin 3) K

abbrev PSL3 (K : Type) [Field K] : Type := SL3 K ⧸ Subgroup.center (SL3 K)

variable {K : Type} [Field K]

abbrev rt {i j : Fin 3} (h : i ≠ j) (s : K) : SL3 K := Matrix.SpecialLinearGroup.transvection h s

theorem rt_apply {i j : Fin 3} (h : i ≠ j) (s : K) (a b : Fin 3) :
    ((rt h s : SL3 K) : Matrix (Fin 3) (Fin 3) K) a b =
      (if a = b then 1 else 0) + (if i = a ∧ j = b then s else 0) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]

theorem rt_apply_diag {i j : Fin 3} (h : i ≠ j) (s : K) (a : Fin 3) :
    ((rt h s : SL3 K) : Matrix (Fin 3) (Fin 3) K) a a = 1 := by
  rw [rt_apply]
  by_cases ha : i = a ∧ j = a
  · exact absurd (ha.1.trans ha.2.symm) h
  · simp [ha]

theorem rt_apply_self {i j : Fin 3} (h : i ≠ j) (s : K) :
    ((rt h s : SL3 K) : Matrix (Fin 3) (Fin 3) K) i j = s := by
  rw [rt_apply]
  simp [h]

theorem rt_apply_of_ne {i j : Fin 3} (h : i ≠ j) (s : K) {a b : Fin 3} (hab : a ≠ b)
    (hij : ¬ (i = a ∧ j = b)) :
    ((rt h s : SL3 K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  rw [rt_apply]
  simp [hab, hij]

theorem rt_add {i j : Fin 3} (h : i ≠ j) (s s' : K) : rt h (s + s') = rt h s * rt h s' :=
  Matrix.SpecialLinearGroup.transvection_add h s s'

theorem rt_zero {i j : Fin 3} (h : i ≠ j) : (rt h (0 : K) : SL3 K) = 1 :=
  Matrix.SpecialLinearGroup.transvection_coeff_zero h

theorem rt_mul_self [CharP K 2] {i j : Fin 3} (h : i ≠ j) (s : K) : rt h s * rt h s = 1 := by
  rw [← rt_add, CharTwo.add_self_eq_zero, rt_zero]

theorem rt_inv [CharP K 2] {i j : Fin 3} (h : i ≠ j) (s : K) : (rt h s)⁻¹ = rt h s :=
  inv_eq_of_mul_eq_one_right (rt_mul_self h s)

theorem commute_rt {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (s s' : K) : Commute (rt hij s) (rt hkl s') :=
  Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli s s'

theorem not_commute_rt_chain {i j l : Fin 3} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) {s s' : K}
    (hs : s ≠ 0) (hs' : s' ≠ 0) : ¬ Commute (rt hij s) (rt hjl s') := by
  intro hc
  have h1 := Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil s s'
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.eq] at h1
  have h2 : rt hil (s * s') ∈ Subgroup.center (SL3 K) := by
    rw [show rt hil (s * s') = 1 from h1.symm]
    exact Subgroup.one_mem _
  rw [Matrix.SpecialLinearGroup.transvection_mem_center_iff] at h2
  exact mul_ne_zero hs hs' h2

theorem not_commute_rt_opp {i j : Fin 3} (hij : i ≠ j) {s s' : K} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    ¬ Commute (rt hij s) (rt hij.symm s') := by
  intro hc
  have h1 := congrArg (fun g : SL3 K => (g : Matrix (Fin 3) (Fin 3) K)) hc.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same] at h1
  have h2 := congrFun (congrFun h1 i) i
  simp [Matrix.add_apply, hij.symm] at h2
  exact mul_ne_zero hs hs' (by simpa [mul_comm] using h2)

theorem exists_scalar_of_mem_center {z : SL3 K} (hz : z ∈ Subgroup.center (SL3 K)) :
    ∃ r : K, r ^ 3 = 1 ∧ (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) r := by
  obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  exact ⟨r, by simpa using hr, hzr.symm⟩

theorem center_pow_three {z : SL3 K} (hz : z ∈ Subgroup.center (SL3 K)) : z ^ 3 = 1 := by
  obtain ⟨r, hr, hzr⟩ := exists_scalar_of_mem_center hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hzr, ← map_pow, hr, map_one]
  rfl

theorem center_eq_one_of_sq {z : SL3 K} (hz : z ∈ Subgroup.center (SL3 K)) (h : z * z = 1) :
    z = 1 := by
  have h3 := center_pow_three hz
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h
  calc z = z * (z * z) := by rw [h, mul_one]
    _ = z ^ 3 := by rw [pow_succ, pow_two]; group
    _ = 1 := h3


theorem commute_of_mk_commute {x y : SL3 K} (hx : x * x = 1) (hy : y * y = 1)
    (h : Commute (QuotientGroup.mk x : PSL3 K) (QuotientGroup.mk y)) : Commute x y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : (QuotientGroup.mk (x * y) : PSL3 K) = QuotientGroup.mk (y * x) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h.eq
  rw [QuotientGroup.eq] at h1
  have hz_eq : (x * y)⁻¹ * (y * x) = (y * x) * (y * x) := by
    rw [_root_.mul_inv_rev, hxi, hyi]
  rw [hz_eq] at h1
  have hw : x * (y * x) * x⁻¹ = (y * x)⁻¹ := by
    rw [_root_.mul_inv_rev, hxi, hyi]
    calc x * (y * x) * x = x * y * (x * x) := by group
      _ = x * y := by rw [hx, mul_one]
  have hconj : x * ((y * x) * (y * x)) * x⁻¹ = ((y * x) * (y * x))⁻¹ := by
    calc x * ((y * x) * (y * x)) * x⁻¹ = (x * (y * x) * x⁻¹) * (x * (y * x) * x⁻¹) := by group
      _ = (y * x)⁻¹ * (y * x)⁻¹ := by rw [hw]
      _ = ((y * x) * (y * x))⁻¹ := (_root_.mul_inv_rev (y * x) (y * x)).symm
  have hcen := (Subgroup.mem_center_iff.mp h1) x
  have hzz : ((y * x) * (y * x)) = ((y * x) * (y * x))⁻¹ := by
    calc ((y * x) * (y * x)) = x * ((y * x) * (y * x)) * x⁻¹ := by
          rw [hcen, mul_inv_cancel_right]
      _ = ((y * x) * (y * x))⁻¹ := hconj
  have hsq : ((y * x) * (y * x)) * ((y * x) * (y * x)) = 1 := by
    nth_rewrite 2 [hzz]
    exact mul_inv_cancel _
  have hz1 := center_eq_one_of_sq h1 hsq
  have h3 : (y * x)⁻¹ = y * x := inv_eq_of_mul_eq_one_right hz1
  rw [_root_.mul_inv_rev, hxi, hyi] at h3
  exact h3

theorem exists_involution_lift {u : PSL3 K} (hu : u * u = 1) :
    ∃ x : SL3 K, x * x = 1 ∧ (QuotientGroup.mk x : PSL3 K) = u := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
  have hy : y * y ∈ Subgroup.center (SL3 K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hu
  refine ⟨y * (y * y), ?_, ?_⟩
  · have h3 := center_pow_three hy
    calc y * (y * y) * (y * (y * y)) = (y * y) ^ 3 := by rw [pow_three]; group
      _ = 1 := h3
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk y : PSL3 K) * QuotientGroup.mk y = 1 := hu
    rw [this, mul_one]

theorem eq_of_mk_eq_of_involution {x y : SL3 K} (hx : x * x = 1) (hy : y * y = 1)
    (h : (QuotientGroup.mk x : PSL3 K) = QuotientGroup.mk y) : x = y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [QuotientGroup.eq] at h
  set z := x⁻¹ * y with hz
  have hyz : y = x * z := by rw [hz]; group
  have hzz : z * z = 1 := by
    have hc := (Subgroup.mem_center_iff.mp h) x
    have : y * y = z * z := by
      calc y * y = (x * z) * (x * z) := by rw [← hyz]
        _ = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hc]
        _ = (x * x) * (z * z) := by group
        _ = z * z := by rw [hx, one_mul]
    rw [← this, hy]
  have hz1 := center_eq_one_of_sq h hzz
  rw [hyz, hz1, mul_one]

theorem rt_eq_of_mk_eq {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) {s s' : K} (hs : s ≠ 0)
    (h : (QuotientGroup.mk (rt hij s) : PSL3 K) = QuotientGroup.mk (rt hkl s')) :
    i = k ∧ j = l ∧ s = s' := by
  rw [QuotientGroup.eq] at h
  obtain ⟨r, hr, hzr⟩ := exists_scalar_of_mem_center h
  have h1 : ((rt hkl s' : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      ((rt hij s : SL3 K) : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) r := by
    rw [← hzr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h2 : ∀ a b : Fin 3, ((rt hkl s' : SL3 K) : Matrix (Fin 3) (Fin 3) K) a b =
      ((rt hij s : SL3 K) : Matrix (Fin 3) (Fin 3) K) a b * r := by
    intro a b
    rw [h1, Matrix.scalar_apply, Matrix.mul_diagonal]
  have hr1 : r = 1 := by
    have := h2 0 0
    rw [rt_apply_diag, rt_apply_diag, one_mul] at this
    exact this.symm
  have h3 := h2 i j
  rw [hr1, mul_one, rt_apply_self, rt_apply] at h3
  by_cases hc : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := hc
    simp [hij] at h3
    exact ⟨rfl, rfl, h3.symm⟩
  · exfalso
    apply hs
    simp [hij, hc] at h3
    exact h3.symm

abbrev ent (x : SL3 K) (a b : Fin 3) : K := (x : Matrix (Fin 3) (Fin 3) K) a b

theorem ent_rt {i j : Fin 3} (h : i ≠ j) (s : K) (a b : Fin 3) :
    ent (rt h s) a b = (if a = b then 1 else 0) + (if i = a ∧ j = b then s else 0) :=
  rt_apply h s a b

theorem ent_ext {x y : SL3 K} (h : ∀ a b, ent x a b = ent y a b) : x = y :=
  Subtype.ext (Matrix.ext h)

theorem ent_mul (x y : SL3 K) (a b : Fin 3) :
    ent (x * y) a b = ∑ k, ent x a k * ent y k b := by
  simp [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

theorem sum_three {M : Type*} [AddCommMonoid M] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (f : Fin 3 → M) : ∑ k, f k = f a + f b + f c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hac
    | exact absurd rfl hbc
    | (simp [Fin.sum_univ_three] <;> abel)

theorem cover_three : ∀ {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → ∀ i : Fin 3,
    i = a ∨ i = b ∨ i = c := by
  decide

end CFSG.RankThree.PartOne.KFOUT3
