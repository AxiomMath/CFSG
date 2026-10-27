module

public import CFSG.Quasithin.Background.RonanH154Gen
public import CFSG.Quasithin.Background.RonanH164Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem dq_check_kl : ∀ u < 32, ∀ m ∈ combos w6, act10 (nq2Arr u) m ^^^ m ∈ combos w1 := by
  decide +kernel

theorem dq_combos_c1 : ∀ d ∈ combos w1, d = 0 ∨ d = 128 := by
  decide +kernel

theorem dq_check_fix_c : ∀ u < 32, act10 (nq2Arr u) 128 = 128 := by
  decide +kernel

theorem dq_check_faithful : ∀ u < 32, u ≠ 0 → ∃ m ∈ combos w6, act10 (nq2Arr u) m ≠ m := by
  decide +kernel

theorem dq_mem_mog22plus {k : P24} (hk : k ∈ NQ2) : k ∈ mog22plus := (NQ2_le_MY_Q hk).1

theorem dq_R_nq2 (u : Fin 32) (m : ℕ) {h : nq2Perm u ∈ mog22plus} :
    Rc ⟨nq2Perm u, h⟩ (toW 10 m) = toW 10 (act10 (nq2Arr u) m) :=
  Rc_nq2 u m

theorem dq_R_nq2_xor (u : Fin 32) (m : ℕ) {h : nq2Perm u ∈ mog22plus} :
    Rc ⟨nq2Perm u, h⟩ (toW 10 m) = toW 10 (act10 (nq2Arr u) m ^^^ m) * toW 10 m := by
  rw [dq_R_nq2, ← toW_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem dq_fix_c {k : P24} (hk : k ∈ NQ2) :
    Rc ⟨k, dq_mem_mog22plus hk⟩ (toW 10 128) = toW 10 128 := by
  obtain ⟨u, rfl⟩ := mem_NQ2_iff.1 hk
  rw [dq_R_nq2, dq_check_fix_c u u.2]

theorem dq_R_mul {k k' : P24} (hk : k ∈ NQ2) (hk' : k' ∈ NQ2) (y : W10) :
    Rc ⟨k * k', dq_mem_mog22plus (mul_mem hk hk')⟩ y =
      Rc ⟨k, dq_mem_mog22plus hk⟩ (Rc ⟨k', dq_mem_mog22plus hk'⟩ y) := by
  have e : (⟨k * k', dq_mem_mog22plus (mul_mem hk hk')⟩ : ↥mog22plus) =
      ⟨k, dq_mem_mog22plus hk⟩ * ⟨k', dq_mem_mog22plus hk'⟩ := rfl
  rw [e, map_mul, MulAut.mul_apply]

theorem dq_R_mul_c {k : P24} (hk : k ∈ NQ2) (y : W10) :
    Rc ⟨k, dq_mem_mog22plus hk⟩ (y * toW 10 128) =
      Rc ⟨k, dq_mem_mog22plus hk⟩ y * toW 10 128 := by
  rw [map_mul, dq_fix_c hk]

theorem dq_KL {x : W10} (hx : x ∈ X6) {k : P24} (hk : k ∈ NQ2) :
    Rc ⟨k, dq_mem_mog22plus hk⟩ x = x ∨ Rc ⟨k, dq_mem_mog22plus hk⟩ x = x * toW 10 128 := by
  obtain ⟨u, rfl⟩ := mem_NQ2_iff.1 hk
  have hx' : x ∈ maskSub 10 w6 := hx
  obtain ⟨m, hm, rfl⟩ := mem_maskSub.1 hx'
  rw [dq_R_nq2_xor]
  rcases dq_combos_c1 _ (dq_check_kl u u.2 m hm) with h0 | h0
  · left
    rw [h0, toW_zero, one_mul]
  · right
    rw [h0]
    exact mul_comm _ _

theorem dq_c_mul_self : toW 10 128 * toW 10 128 = 1 := by
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem dq_c_ne_one : toW 10 128 ≠ 1 := by
  intro h
  have h' : toW 10 128 = toW 10 0 := by
    rw [toW_zero]
    exact h
  exact absurd (toW_inj (by norm_num) (by norm_num) h') (by norm_num)

theorem dq_ne (x : W10) : x * toW 10 128 ≠ x := fun h =>
  dq_c_ne_one (mul_left_cancel (h.trans (mul_one x).symm))

theorem dq_mul_c_ne (x y : W10) : x * (y * toW 10 128) ≠ x * y := fun h =>
  dq_c_ne_one (mul_left_cancel ((mul_left_cancel h).trans (mul_one y).symm))

theorem dq_mul_c_ne' (x y : W10) : x * y * toW 10 128 ≠ x * y := fun h =>
  dq_c_ne_one (mul_left_cancel (h.trans (mul_one (x * y)).symm))

theorem dq_mul_c_ne'' (x y : W10) : x * toW 10 128 * y ≠ x * y := by
  rw [mul_right_comm]
  exact dq_mul_c_ne' x y

theorem dq_mul_c_sq (x y : W10) : x * toW 10 128 * (y * toW 10 128) = x * y := by
  rw [mul_mul_mul_comm, dq_c_mul_self, mul_one]

theorem dq_c_sq_mul (x : W10) : x * toW 10 128 * toW 10 128 = x := by
  rw [mul_assoc, dq_c_mul_self, mul_one]

open scoped Classical in
noncomputable def dqPr (x : W10) (k : P24) : ZMod 2 :=
  if h : k ∈ mog22plus then (if Rc ⟨k, h⟩ x = x then 0 else 1) else 0

open scoped Classical in
theorem dqPr_eq {x : W10} {k : P24} (hk : k ∈ mog22plus) :
    dqPr x k = if Rc ⟨k, hk⟩ x = x then 0 else 1 := by
  unfold dqPr
  exact dif_pos hk

theorem dqPr_eq_fix {x : W10} {k : P24} (hk : k ∈ NQ2) :
    dqPr x k = if Rc ⟨k, dq_mem_mog22plus hk⟩ x = x then 0 else 1 :=
  dqPr_eq (dq_mem_mog22plus hk)

theorem dq_P1 {x : W10} (hx : x ∈ X6) {k k' : P24} (hk : k ∈ NQ2) (hk' : k' ∈ NQ2) :
    dqPr x (k * k') = dqPr x k + dqPr x k' := by
  rw [dqPr_eq_fix (mul_mem hk hk'), dqPr_eq_fix hk, dqPr_eq_fix hk',
    dq_R_mul hk hk' x]
  rcases dq_KL hx hk with h1 | h1 <;> rcases dq_KL hx hk' with h2 | h2
  · rw [h2, h1]
    simp
  · rw [h2, dq_R_mul_c hk, h1]
    simp [dq_ne x, dq_c_ne_one]
  · rw [h2, h1]
    simp [dq_ne x, dq_c_ne_one]
  · rw [h2, dq_R_mul_c hk, h1]
    simp [dq_c_sq_mul, dq_ne x, dq_c_ne_one] <;> decide

theorem dq_P2 {x x' : W10} (hx : x ∈ X6) (hx' : x' ∈ X6) {k : P24} (hk : k ∈ NQ2) :
    dqPr (x * x') k = dqPr x k + dqPr x' k := by
  rw [dqPr_eq_fix hk, dqPr_eq_fix hk, dqPr_eq_fix hk, map_mul]
  rcases dq_KL hx hk with h1 | h1 <;> rcases dq_KL hx' hk with h2 | h2
  · rw [h1, h2]
    simp
  · rw [h1, h2]
    simp [dq_mul_c_ne x x', dq_ne x', dq_c_ne_one]
  · rw [h1, h2]
    simp [dq_mul_c_ne'' x x', dq_ne x, dq_c_ne_one]
  · rw [h1, h2]
    simp [dq_mul_c_sq x x', dq_ne x, dq_ne x'] <;> decide

theorem dq_mem_rImg {k : P24} (hk : k ∈ NQ2) :
    Rc ⟨k, dq_mem_mog22plus hk⟩ ∈ rImg Rc NQ2 :=
  Subgroup.mem_map_of_mem Rc
    (show (⟨k, dq_mem_mog22plus hk⟩ : ↥mog22plus) ∈ NQ2.subgroupOf mog22plus from hk)

theorem dq_P3 {x : W10} (hx : x ∈ fixV (rImg Rc NQ2)) {k : P24} (hk : k ∈ NQ2) :
    dqPr x k = 0 := by
  rw [dqPr_eq_fix hk]
  exact if_pos (mem_fixV.1 hx _ (dq_mem_rImg hk))

theorem dq_P4 {x : W10} (hx : x ∉ fixV (rImg Rc NQ2)) : ∃ k ∈ NQ2, dqPr x k ≠ 0 := by
  have hex : ∃ g ∈ rImg Rc NQ2, g x ≠ x := by
    by_contra hcon
    exact hx (mem_fixV.2 fun g hg => Classical.byContradiction fun h => hcon ⟨g, hg, h⟩)
  obtain ⟨g, hg, hgx⟩ := hex
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  refine ⟨(y : P24), hy, ?_⟩
  have hgx' : ¬ (Rc ⟨(y : P24), y.2⟩ x = x) := hgx
  rw [dqPr_eq y.2, if_neg hgx']
  decide

theorem dq_P5 {k : P24} (hk : k ∈ NQ2) (hk1 : k ≠ 1) : ∃ x ∈ X6, dqPr x k ≠ 0 := by
  obtain ⟨u, rfl⟩ := mem_NQ2_iff.1 hk
  have hu : (u : ℕ) ≠ 0 := by
    intro h
    have hu0 : u = 0 := Fin.ext h
    subst hu0
    exact hk1 nq2Perm_zero
  obtain ⟨m, hm, hmne⟩ := dq_check_faithful u u.2 hu
  have hlt : m < 2 ^ 10 := combos_lt mask_lt_w6 m hm
  have hne : toW 10 (act10 (nq2Arr u) m) ≠ toW 10 m := fun h =>
    hmne (toW_inj (act10_lt _ _) hlt h)
  refine ⟨toW 10 m, toW_mem_maskSub hm, ?_⟩
  rw [dqPr_eq_fix hk, dq_R_nq2, if_neg hne]
  decide

theorem dq_P6 (g : ↥mog22plus) {x : W10} {k : P24} (hk : k ∈ NQ2) :
    dqPr (Rc g x) ((g : P24) * k * (g : P24)⁻¹) = dqPr x k := by
  have hk' : k ∈ mog22plus := dq_mem_mog22plus hk
  have hgk : (g : P24) * k * (g : P24)⁻¹ ∈ mog22plus :=
    mul_mem (mul_mem g.2 hk') (inv_mem g.2)
  have hconj : Rc ⟨(g : P24) * k * (g : P24)⁻¹, hgk⟩ = Rc g * Rc ⟨k, hk'⟩ * (Rc g)⁻¹ := by
    have e : (⟨(g : P24) * k * (g : P24)⁻¹, hgk⟩ : ↥mog22plus) = g * ⟨k, hk'⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  rw [dqPr_eq hgk, dqPr_eq hk', hconj, MulAut.mul_apply, MulAut.mul_apply,
    MulAut.inv_apply_self]
  by_cases h : Rc ⟨k, hk'⟩ x = x
  · simp [h]
  · have hne : ¬ (Rc g (Rc ⟨k, hk'⟩ x) = Rc g x) := fun e => h (MulEquiv.injective (Rc g) e)
    rw [if_neg h, if_neg hne]

theorem dual_std_X :
    IsDualOfConj Rc (MY mog22plus Qstd) X6 (fixV (rImg Rc (KY mog22plus Qstd)))
      (KY mog22plus Qstd) := by
  rw [KY_Q_L2]
  unfold IsDualOfConj
  refine ⟨dqPr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    exact dq_P1 hx hk hk'
  · intro x hx x' hx' k hk
    exact dq_P2 hx hx' hk
  · intro x hx k hk
    exact dq_P3 hx hk
  · intro x _ hx
    exact dq_P4 hx
  · intro k hk hk1
    exact dq_P5 hk hk1
  · intro g _ x _ k hk
    exact dq_P6 g hk

end CFSG.Quasithin.RonanH154
