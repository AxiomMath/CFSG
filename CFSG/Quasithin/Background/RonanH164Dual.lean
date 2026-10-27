module

public import CFSG.Quasithin.Background.RonanH143QH
public import CFSG.Quasithin.Background.RonanH164Base
public import CFSG.Quasithin.Background.RonanH164Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem dual_check_kl : ∀ t : Fin 16, ∀ m ∈ combos c5, actC10 (koArr t) m ^^^ m ∈ combos c1 := by
  decide +kernel

theorem dual_combos_c1 : ∀ d ∈ combos c1, d = 0 ∨ d = 1 := by
  decide +kernel

theorem dual_check_fix_one : ∀ t : Fin 16, actC10 (koArr t) 1 = 1 := by
  decide +kernel

theorem dual_check_faithful : ∀ t : Fin 16, t ≠ 0 → ∃ m ∈ combos c5, actC10 (koArr t) m ≠ m := by
  decide +kernel

theorem dual_c5_lt : ∀ a ∈ c5, a < 2 ^ 10 := by
  decide +kernel

theorem dual_koArr_zero : koArr ((0 : Fin 16) : ℕ) = idArr := by
  decide +kernel

theorem dual_koPerm_zero : koPerm 0 = 1 := by
  have h1 : HasArr (koPerm 0) (koArr ((0 : Fin 16) : ℕ)) := hasArr_permOfArr (koArr_ok 0).1
  rw [dual_koArr_zero] at h1
  exact perm_eq_of_hasArr h1 hasArr_one

theorem dual_mem_mog22plus {k : P24} (hk : k ∈ fixO) : k ∈ mog22plus := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff k).1 hk
  exact mog22_le_mog22plus (koPerm_mem_mog22 t)

theorem dual_R_koPerm (t : Fin 16) (m : ℕ) {h : koPerm t ∈ mog22plus} :
    R ⟨koPerm t, h⟩ (toW 10 m) = toW 10 (actC10 (koArr t) m) :=
  R_ko t m

theorem dual_R_koPerm_xor (t : Fin 16) (m : ℕ) {h : koPerm t ∈ mog22plus} :
    R ⟨koPerm t, h⟩ (toW 10 m) = toW 10 (actC10 (koArr t) m ^^^ m) * toW 10 m := by
  rw [dual_R_koPerm, ← toW_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem dual_fix_c {k : P24} (hk : k ∈ fixO) :
    R ⟨k, dual_mem_mog22plus hk⟩ (toW 10 1) = toW 10 1 := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff k).1 hk
  rw [dual_R_koPerm, dual_check_fix_one t]

theorem dual_R_mul_c {k : P24} (hk : k ∈ fixO) (y : W10) :
    R ⟨k, dual_mem_mog22plus hk⟩ (y * toW 10 1) =
      R ⟨k, dual_mem_mog22plus hk⟩ y * toW 10 1 := by
  rw [map_mul, dual_fix_c hk]

theorem dual_R_mul {k k' : P24} (hk : k ∈ fixO) (hk' : k' ∈ fixO) (y : W10) :
    R ⟨k * k', dual_mem_mog22plus (mul_mem hk hk')⟩ y =
      R ⟨k, dual_mem_mog22plus hk⟩ (R ⟨k', dual_mem_mog22plus hk'⟩ y) := by
  have e : (⟨k * k', dual_mem_mog22plus (mul_mem hk hk')⟩ : ↥mog22plus) =
      ⟨k, dual_mem_mog22plus hk⟩ * ⟨k', dual_mem_mog22plus hk'⟩ := rfl
  rw [e, map_mul, MulAut.mul_apply]

theorem dual_KL {x : W10} (hx : x ∈ V5) {k : P24} (hk : k ∈ fixO) :
    R ⟨k, dual_mem_mog22plus hk⟩ x = x ∨ R ⟨k, dual_mem_mog22plus hk⟩ x = x * toW 10 1 := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff k).1 hk
  have hx' : x ∈ maskSub 10 c5 := hx
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hx'
  rw [dual_R_koPerm_xor]
  rcases dual_combos_c1 _ (dual_check_kl t m hm) with h0 | h0
  · left
    rw [h0, toW_zero, one_mul]
  · right
    rw [h0]
    exact mul_comm _ _

theorem dual_c_mul_self : toW 10 1 * toW 10 1 = 1 := by
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem dual_c_ne_one : toW 10 1 ≠ 1 := by
  intro h
  have h' : toW 10 1 = toW 10 0 := by
    rw [toW_zero]
    exact h
  exact one_ne_zero (toW_inj (by norm_num) (by norm_num) h')

theorem dual_ne (x : W10) : x * toW 10 1 ≠ x := fun h =>
  dual_c_ne_one (mul_left_cancel (h.trans (mul_one x).symm))

theorem dual_mul_c_ne (x y : W10) : x * (y * toW 10 1) ≠ x * y := fun h =>
  dual_c_ne_one (mul_left_cancel ((mul_left_cancel h).trans (mul_one y).symm))

theorem dual_mul_c_ne' (x y : W10) : x * y * toW 10 1 ≠ x * y := fun h =>
  dual_c_ne_one (mul_left_cancel (h.trans (mul_one (x * y)).symm))

theorem dual_mul_c_ne'' (x y : W10) : x * toW 10 1 * y ≠ x * y := by
  rw [mul_right_comm]
  exact dual_mul_c_ne' x y

theorem dual_mul_c_sq (x y : W10) : x * toW 10 1 * (y * toW 10 1) = x * y := by
  rw [mul_mul_mul_comm, dual_c_mul_self, mul_one]

theorem dual_c_sq_mul (x : W10) : x * toW 10 1 * toW 10 1 = x := by
  rw [mul_assoc, dual_c_mul_self, mul_one]

open scoped Classical in
noncomputable def dualPr (x : W10) (k : P24) : ZMod 2 :=
  if h : k ∈ mog22plus then (if R ⟨k, h⟩ x = x then 0 else 1) else 0

open scoped Classical in
theorem dualPr_eq {x : W10} {k : P24} (hk : k ∈ mog22plus) :
    dualPr x k = if R ⟨k, hk⟩ x = x then 0 else 1 := by
  unfold dualPr
  exact dif_pos hk

theorem dualPr_eq_fix {x : W10} {k : P24} (hk : k ∈ fixO) :
    dualPr x k = if R ⟨k, dual_mem_mog22plus hk⟩ x = x then 0 else 1 :=
  dualPr_eq (dual_mem_mog22plus hk)

theorem dual_P1 {x : W10} (hx : x ∈ V5) {k k' : P24} (hk : k ∈ fixO) (hk' : k' ∈ fixO) :
    dualPr x (k * k') = dualPr x k + dualPr x k' := by
  rw [dualPr_eq_fix (mul_mem hk hk'), dualPr_eq_fix hk, dualPr_eq_fix hk',
    dual_R_mul hk hk' x]
  rcases dual_KL hx hk with h1 | h1 <;> rcases dual_KL hx hk' with h2 | h2
  · rw [h2, h1]
    simp
  · rw [h2, dual_R_mul_c hk, h1]
    simp [dual_ne x, dual_c_ne_one]
  · rw [h2, h1]
    simp [dual_ne x, dual_c_ne_one]
  · rw [h2, dual_R_mul_c hk, h1]
    simp [dual_c_sq_mul, dual_ne x, dual_c_ne_one] <;> decide

theorem dual_P2 {x x' : W10} (hx : x ∈ V5) (hx' : x' ∈ V5) {k : P24} (hk : k ∈ fixO) :
    dualPr (x * x') k = dualPr x k + dualPr x' k := by
  rw [dualPr_eq_fix hk, dualPr_eq_fix hk, dualPr_eq_fix hk, map_mul]
  rcases dual_KL hx hk with h1 | h1 <;> rcases dual_KL hx' hk with h2 | h2
  · rw [h1, h2]
    simp
  · rw [h1, h2]
    simp [dual_mul_c_ne x x', dual_ne x', dual_c_ne_one]
  · rw [h1, h2]
    simp [dual_mul_c_ne'' x x', dual_ne x, dual_c_ne_one]
  · rw [h1, h2]
    simp [dual_mul_c_sq x x', dual_ne x, dual_ne x'] <;> decide

theorem dual_mem_rImg {k : P24} (hk : k ∈ fixO) :
    R ⟨k, dual_mem_mog22plus hk⟩ ∈ rImg R fixO :=
  Subgroup.mem_map_of_mem R
    (show (⟨k, dual_mem_mog22plus hk⟩ : ↥mog22plus) ∈ fixO.subgroupOf mog22plus from hk)

theorem dual_P3 {x : W10} (hx : x ∈ fixV (rImg R fixO)) {k : P24} (hk : k ∈ fixO) :
    dualPr x k = 0 := by
  rw [dualPr_eq_fix hk]
  exact if_pos (mem_fixV.1 hx _ (dual_mem_rImg hk))

theorem dual_P4 {x : W10} (hx : x ∉ fixV (rImg R fixO)) : ∃ k ∈ fixO, dualPr x k ≠ 0 := by
  have hex : ∃ g ∈ rImg R fixO, g x ≠ x := by
    by_contra hcon
    exact hx (mem_fixV.2 fun g hg => Classical.byContradiction fun h => hcon ⟨g, hg, h⟩)
  obtain ⟨g, hg, hgx⟩ := hex
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  refine ⟨(y : P24), hy, ?_⟩
  have hgx' : ¬ (R ⟨(y : P24), y.2⟩ x = x) := hgx
  rw [dualPr_eq y.2, if_neg hgx']
  decide

theorem dual_P5 {k : P24} (hk : k ∈ fixO) (hk1 : k ≠ 1) : ∃ x ∈ V5, dualPr x k ≠ 0 := by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff k).1 hk
  have ht : t ≠ 0 := by
    rintro rfl
    exact hk1 dual_koPerm_zero
  obtain ⟨m, hm, hmne⟩ := dual_check_faithful t ht
  have hlt : m < 2 ^ 10 := combos_lt dual_c5_lt m hm
  have hne : toW 10 (actC10 (koArr t) m) ≠ toW 10 m := fun h =>
    hmne (toW_inj (actC10_lt _ _) hlt h)
  refine ⟨toW 10 m, toW_mem_maskSub hm, ?_⟩
  rw [dualPr_eq_fix hk, dual_R_koPerm, if_neg hne]
  decide

theorem dual_P6 (g : ↥mog22plus) {x : W10} {k : P24} (hk : k ∈ fixO) :
    dualPr (R g x) ((g : P24) * k * (g : P24)⁻¹) = dualPr x k := by
  have hk' : k ∈ mog22plus := dual_mem_mog22plus hk
  have hgk : (g : P24) * k * (g : P24)⁻¹ ∈ mog22plus :=
    mul_mem (mul_mem g.2 hk') (inv_mem g.2)
  have hconj : R ⟨(g : P24) * k * (g : P24)⁻¹, hgk⟩ = R g * R ⟨k, hk'⟩ * (R g)⁻¹ := by
    have e : (⟨(g : P24) * k * (g : P24)⁻¹, hgk⟩ : ↥mog22plus) = g * ⟨k, hk'⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  rw [dualPr_eq hgk, dualPr_eq hk', hconj, MulAut.mul_apply, MulAut.mul_apply,
    MulAut.inv_apply_self]
  by_cases h : R ⟨k, hk'⟩ x = x
  · simp [h]
  · have hne : ¬ (R g (R ⟨k, hk'⟩ x) = R g x) := fun e => h (MulEquiv.injective (R g) e)
    rw [if_neg h, if_neg hne]

theorem dual_std :
    IsDualOfConj R (MY mog22plus Hstd) V5 (fixV (rImg R (KY mog22plus Hstd)))
      (KY mog22plus Hstd) := by
  rw [KY_H_L2]
  unfold IsDualOfConj
  refine ⟨dualPr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    exact dual_P1 hx hk hk'
  · intro x hx x' hx' k hk
    exact dual_P2 hx hx' hk
  · intro x hx k hk
    exact dual_P3 hx hk
  · intro x _ hx
    exact dual_P4 hx
  · intro k hk hk1
    exact dual_P5 hk hk1
  · intro g _ x _ k hk
    exact dual_P6 g hk

end CFSG.Quasithin.RonanH163
