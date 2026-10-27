module

public import CFSG.Quasithin.Background.SimsF5Form

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open scoped Matrix Pointwise

local notation "M6" => Matrix (Fin 6) (Fin 6) (ZMod 3)

@[expose] def quatZpow {G : Type*} [Group G] {n : ℕ} [NeZero n] (A : G) (k : ZMod n) : G :=
  A ^ k.val

theorem quatZpow_add {G : Type*} [Group G] {n : ℕ} [NeZero n] {A : G} (hA : A ^ n = 1)
    (i j : ZMod n) : quatZpow A (i + j) = quatZpow A i * quatZpow A j := by
  unfold quatZpow
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hA, pow_add]

theorem quatZpow_zero {G : Type*} [Group G] {n : ℕ} [NeZero n] (A : G) :
    quatZpow A (0 : ZMod n) = 1 := by
  simp [quatZpow]

theorem quatZpow_neg {G : Type*} [Group G] {n : ℕ} [NeZero n] {A : G} (hA : A ^ n = 1)
    (i : ZMod n) : quatZpow A (-i) = (quatZpow A i)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← quatZpow_add hA, neg_add_cancel, quatZpow_zero]

theorem quatZpow_mul_B {G : Type*} [Group G] {n : ℕ} [NeZero n] {A B : G}
    (hA : A ^ n = 1) (hBA : B * A * B⁻¹ = A⁻¹) (i : ZMod n) :
    quatZpow A i * B = B * quatZpow A (-i) := by
  rw [quatZpow_neg hA]
  have h1 : B * A ^ i.val * B⁻¹ = (A ^ i.val)⁻¹ := by
    rw [← conj_pow, hBA, inv_pow]
  have h2 : B * (A ^ i.val)⁻¹ * B⁻¹ = A ^ i.val := by
    have := congrArg (·⁻¹) h1
    simpa [mul_assoc] using this
  calc quatZpow A i * B = (B * (A ^ i.val)⁻¹ * B⁻¹) * B := by rw [quatZpow, h2]
    _ = B * (quatZpow A i)⁻¹ := by simp [mul_assoc, quatZpow]

@[expose] def quatFun {G : Type*} [Group G] (A B : G) : QuaternionGroup 2 → G
  | .a k => quatZpow A k
  | .xa k => B * quatZpow A k

@[expose] def quatLift {G : Type*} [Group G] (A B : G) (hA : A ^ 4 = 1) (hB : B ^ 2 = A ^ 2)
    (hBA : B * A * B⁻¹ = A⁻¹) : QuaternionGroup 2 →* G where
  toFun := quatFun A B
  map_one' := by
    rw [← QuaternionGroup.a_zero]
    simp [quatFun, quatZpow_zero]
  map_mul' := by
    have hA' : A ^ (2 * 2) = 1 := hA
    rintro (i | i) (j | j)
    · simp only [QuaternionGroup.a_mul_a, quatFun]
      exact quatZpow_add hA' i j
    · simp only [QuaternionGroup.a_mul_xa, quatFun]
      rw [← mul_assoc, quatZpow_mul_B hA' hBA, mul_assoc, ← quatZpow_add hA', neg_add_eq_sub]
    · simp only [QuaternionGroup.xa_mul_a, quatFun, quatZpow_add hA', mul_assoc]
    · simp only [QuaternionGroup.xa_mul_xa, quatFun]
      have h2 : quatZpow A (((2 : ℕ) : ZMod (2 * 2))) = A ^ 2 := by
        simp only [quatZpow, ZMod.val_natCast]
      have h3 : (((2 : ℕ) : ZMod (2 * 2))) + j - i = ((2 : ℕ) : ZMod (2 * 2)) + (-i + j) := by
        ring
      rw [h3, quatZpow_add hA', h2]
      symm
      calc B * quatZpow A i * (B * quatZpow A j)
          = B * (quatZpow A i * B) * quatZpow A j := by simp only [mul_assoc]
        _ = B * (B * quatZpow A (-i)) * quatZpow A j := by rw [quatZpow_mul_B hA' hBA]
        _ = (B * B) * (quatZpow A (-i) * quatZpow A j) := by simp only [mul_assoc]
        _ = A ^ 2 * quatZpow A (-i + j) := by rw [← quatZpow_add hA', ← hB, sq]

@[expose] def quatD3Fun {G : Type*} [Group G] (A C : G) : DihedralGroup 3 → G
  | .r k => quatZpow A k
  | .sr k => C * quatZpow A k

@[expose] def quatD3Lift {G : Type*} [Group G] (A C : G) (hA : A ^ 3 = 1) (hC : C ^ 2 = 1)
    (hCA : C * A * C⁻¹ = A⁻¹) : DihedralGroup 3 →* G where
  toFun := quatD3Fun A C
  map_one' := by
    rw [← DihedralGroup.r_zero]
    simp [quatD3Fun, quatZpow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · simp only [DihedralGroup.r_mul_r, quatD3Fun]
      exact quatZpow_add hA i j
    · simp only [DihedralGroup.r_mul_sr, quatD3Fun]
      rw [← mul_assoc, quatZpow_mul_B hA hCA, mul_assoc, ← quatZpow_add hA, neg_add_eq_sub]
    · simp only [DihedralGroup.sr_mul_r, quatD3Fun, quatZpow_add hA, mul_assoc]
    · simp only [DihedralGroup.sr_mul_sr, quatD3Fun]
      symm
      calc C * quatZpow A i * (C * quatZpow A j)
          = C * (quatZpow A i * C) * quatZpow A j := by simp only [mul_assoc]
        _ = C * (C * quatZpow A (-i)) * quatZpow A j := by rw [quatZpow_mul_B hA hCA]
        _ = (C * C) * (quatZpow A (-i) * quatZpow A j) := by simp only [mul_assoc]
        _ = quatZpow A (j - i) := by
          rw [← quatZpow_add hA, ← sq, hC, one_mul, neg_add_eq_sub]

@[expose] def quatPermOfD3 : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | .r k => finRotate 3 ^ k.val
  | .sr k => Equiv.swap 0 1 * finRotate 3 ^ k.val

theorem quatPermOfD3_mul :
    ∀ x y : DihedralGroup 3, quatPermOfD3 (x * y) = quatPermOfD3 x * quatPermOfD3 y := by
  decide

theorem quatPermOfD3_bijective : Function.Bijective quatPermOfD3 := by
  decide

@[expose] def quatD3PermEquiv : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (MonoidHom.mk' quatPermOfD3 quatPermOfD3_mul) quatPermOfD3_bijective

@[expose] def quatOfOrth (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (h : M * Mᵀ = 1) : GL6 :=
  ⟨M, Mᵀ, h, mul_eq_one_comm.1 h⟩

@[expose] def quatLiMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 2, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatLjMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 0, 2, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatRiInvMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatRjInvMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    2, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatAMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 0, 2, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 2, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatBMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![2, 1, 2, 1, 0, 0;
    1, 2, 2, 1, 0, 0;
    2, 2, 2, 2, 0, 0;
    2, 2, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatCMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 0, 2, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 2]

@[expose] def quatDMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 2, 0, 0;
    0, 0, 0, 0, 2, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def quatLi : GL6 := quatOfOrth quatLiMat (by decide)
@[expose] def quatLj : GL6 := quatOfOrth quatLjMat (by decide)
@[expose] def quatRiInv : GL6 := quatOfOrth quatRiInvMat (by decide)
@[expose] def quatRjInv : GL6 := quatOfOrth quatRjInvMat (by decide)
@[expose] def quatA : GL6 := quatOfOrth quatAMat (by decide)
@[expose] def quatB : GL6 := quatOfOrth quatBMat (by decide)
@[expose] def quatC : GL6 := quatOfOrth quatCMat (by decide)
@[expose] def quatD : GL6 := quatOfOrth quatDMat (by decide)

theorem quatLi_pow : quatLi ^ 4 = 1 := by decide
theorem quatLj_sq : quatLj ^ 2 = quatLi ^ 2 := by decide
theorem quatLj_conj : quatLj * quatLi * quatLj⁻¹ = quatLi⁻¹ := by decide
theorem quatRiInv_pow : quatRiInv ^ 4 = 1 := by decide
theorem quatRjInv_sq : quatRjInv ^ 2 = quatRiInv ^ 2 := by decide
theorem quatRjInv_conj : quatRjInv * quatRiInv * quatRjInv⁻¹ = quatRiInv⁻¹ := by decide
theorem quatA_pow : quatA ^ 3 = 1 := by decide
theorem quatC_sq : quatC ^ 2 = 1 := by decide
theorem quatC_conj : quatC * quatA * quatC⁻¹ = quatA⁻¹ := by decide
theorem quatB_pow : quatB ^ 3 = 1 := by decide
theorem quatD_sq : quatD ^ 2 = 1 := by decide
theorem quatD_conj : quatD * quatB * quatD⁻¹ = quatB⁻¹ := by decide

@[expose] def quatL : QuaternionGroup 2 →* GL6 :=
  quatLift quatLi quatLj quatLi_pow quatLj_sq quatLj_conj

@[expose] def quatR : QuaternionGroup 2 →* GL6 :=
  quatLift quatRiInv quatRjInv quatRiInv_pow quatRjInv_sq quatRjInv_conj

theorem quatL_commute_quatR (u w : QuaternionGroup 2) : Commute (quatL u) (quatR w) := by
  have hLiRi : Commute quatLi quatRiInv := by unfold Commute SemiconjBy; decide
  have hLiRj : Commute quatLi quatRjInv := by unfold Commute SemiconjBy; decide
  have hLjRi : Commute quatLj quatRiInv := by unfold Commute SemiconjBy; decide
  have hLjRj : Commute quatLj quatRjInv := by unfold Commute SemiconjBy; decide
  rcases u with i | i <;> rcases w with j | j
  · show Commute (quatLi ^ i.val) (quatRiInv ^ j.val)
    exact hLiRi.pow_pow _ _
  · show Commute (quatLi ^ i.val) (quatRjInv * quatRiInv ^ j.val)
    exact (hLiRj.pow_left _).mul_right (hLiRi.pow_pow _ _)
  · show Commute (quatLj * quatLi ^ i.val) (quatRiInv ^ j.val)
    exact (hLjRi.pow_right _).mul_left (hLiRi.pow_pow _ _)
  · show Commute (quatLj * quatLi ^ i.val) (quatRjInv * quatRiInv ^ j.val)
    exact ((hLjRj.mul_right (hLjRi.pow_right _)).mul_left
      ((hLiRj.pow_left _).mul_right (hLiRi.pow_pow _ _)))

@[expose] def q8Hom : QuaternionGroup 2 × QuaternionGroup 2 →* GL6 :=
  MonoidHom.noncommCoprod quatL quatR quatL_commute_quatR

theorem q8Hom_a2_one : q8Hom (QuaternionGroup.a 2, 1) = zDot := by decide

theorem q8Hom_one_a2 : q8Hom (1, QuaternionGroup.a 2) = zDot := by decide

theorem zDot_mem_q8Hom_range : zDot ∈ q8Hom.range :=
  MonoidHom.mem_range.2 ⟨(QuaternionGroup.a 2, 1), q8Hom_a2_one⟩

theorem quat_q8Hom_eq_one :
    ∀ p : QuaternionGroup 2 × QuaternionGroup 2, q8Hom p = 1 →
      p = 1 ∨ p = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  decide

theorem q8Hom_ker : q8Hom.ker = Q8SqK := by
  apply le_antisymm
  · intro p hp
    rcases quat_q8Hom_eq_one p (MonoidHom.mem_ker.1 hp) with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Q8SqK, Subgroup.zpowers_le, MonoidHom.mem_ker]
    decide

theorem quat_card_Q8SqK : Nat.card ↥Q8SqK = 2 := by
  rw [Q8SqK, Nat.card_zpowers]
  exact orderOf_eq_prime (by decide) (by decide)

theorem card_q8Hom_range : Nat.card ↥q8Hom.range = 32 := by
  have h1 : Nat.card ((QuaternionGroup 2 × QuaternionGroup 2) ⧸ q8Hom.ker) =
      Nat.card ↥q8Hom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange q8Hom).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup q8Hom.ker
  have h3 : Nat.card ↥q8Hom.ker = 2 := by rw [q8Hom_ker]; exact quat_card_Q8SqK
  have h4 : Nat.card (QuaternionGroup 2 × QuaternionGroup 2) = 64 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [h1, h3, h4] at h2
  omega

@[expose] def quatReflMat (v : ReflVec) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  1 - qV v.1 • Matrix.vecMulVec v.1 (wv v.1)

theorem quat_reflM_eq (v : ReflVec) : reflM v.1 = quatReflMat v := by
  have h : (qV v.1)⁻¹ = qV v.1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    have := v.2
    generalize qV v.1 = a at this ⊢
    revert a
    decide
  unfold reflM quatReflMat
  rw [h]

theorem quat_val_prod_refl (l : List ReflVec) :
    (((l.map reflOf).prod : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      (l.map quatReflMat).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, List.map_cons, List.prod_cons, reflOf,
      refl6_val, quat_reflM_eq]

theorem quat_mem_MDot_of_refl (l : List ReflVec) (g : GL6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = (l.map quatReflMat).prod)
    (hl : Even l.length) (hc : Even (l.countP fun v => qV v.1 = -1)) : g ∈ MDot := by
  have : g = (l.map reflOf).prod := Units.ext (by rw [hg, quat_val_prod_refl])
  rw [this, prod_refl_mem_MDot_iff]
  exact ⟨hl, hc⟩

@[expose] def quatRV (v : V6) (h : qV v ≠ 0 := by decide) : ReflVec := ⟨v, h⟩

theorem quat_mem_M1Dot {g : GL6} (h1 : g ∈ MDot) (h2 : zDot * g = g * zDot) : g ∈ M1Dot := by
  refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact h2

theorem quatLi_mem_M1Dot : quatLi ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 1, 0, 0, 0, 0], quatRV ![1, 1, 0, 0, 0, 0],
      quatRV ![0, 0, 0, 1, 0, 0], quatRV ![0, 0, 1, 1, 0, 0]] quatLi (by decide) (by decide)
      (by decide))
    (by decide)

theorem quatLj_mem_M1Dot : quatLj ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 1, 0, 1, 0, 0], quatRV ![1, 0, 2, 0, 0, 0],
      quatRV ![0, 0, 0, 1, 0, 0], quatRV ![0, 0, 1, 0, 0, 0]] quatLj (by decide) (by decide)
      (by decide))
    (by decide)

theorem quatRiInv_mem_M1Dot : quatRiInv ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 1, 0, 0, 0, 0], quatRV ![1, 2, 0, 0, 0, 0],
      quatRV ![0, 0, 0, 1, 0, 0], quatRV ![0, 0, 1, 1, 0, 0]] quatRiInv (by decide) (by decide)
      (by decide))
    (by decide)

theorem quatRjInv_mem_M1Dot : quatRjInv ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 1, 0, 1, 0, 0], quatRV ![1, 0, 1, 0, 0, 0],
      quatRV ![0, 0, 0, 1, 0, 0], quatRV ![0, 0, 1, 0, 0, 0]] quatRjInv (by decide) (by decide)
      (by decide))
    (by decide)

theorem quatA_mem_M1Dot : quatA ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 1, 1, 0, 0, 0], quatRV ![1, 0, 1, 0, 0, 0]] quatA
      (by decide) (by decide) (by decide))
    (by decide)

theorem quatB_mem_M1Dot : quatB ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 0, 0, 1, 0, 0], quatRV ![1, 1, 2, 1, 0, 0]] quatB
      (by decide) (by decide) (by decide))
    (by decide)

theorem quatC_mem_M1Dot : quatC ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 0, 0, 0, 0, 1], quatRV ![1, 0, 1, 0, 0, 0]] quatC
      (by decide) (by decide) (by decide))
    (by decide)

theorem quatD_mem_M1Dot : quatD ∈ M1Dot :=
  quat_mem_M1Dot
    (quat_mem_MDot_of_refl [quatRV ![0, 0, 0, 0, 1, 0], quatRV ![0, 0, 0, 1, 0, 0]] quatD
      (by decide) (by decide) (by decide))
    (by decide)

theorem quat_q8_range_le {H : Subgroup GL6} (h1 : quatLi ∈ H) (h2 : quatLj ∈ H)
    (h3 : quatRiInv ∈ H) (h4 : quatRjInv ∈ H) : q8Hom.range ≤ H := by
  rintro _ ⟨⟨u, w⟩, rfl⟩
  have hL : ∀ u, quatL u ∈ H := by
    rintro (k | k)
    · exact H.pow_mem h1 _
    · exact H.mul_mem h2 (H.pow_mem h1 _)
  have hR : ∀ w, quatR w ∈ H := by
    rintro (k | k)
    · exact H.pow_mem h3 _
    · exact H.mul_mem h4 (H.pow_mem h3 _)
  exact H.mul_mem (hL u) (hR w)

theorem q8Hom_range_le : q8Hom.range ≤ M1Dot :=
  quat_q8_range_le quatLi_mem_M1Dot quatLj_mem_M1Dot quatRiInv_mem_M1Dot quatRjInv_mem_M1Dot

theorem quatK_commute (x y : DihedralGroup 3) :
    Commute (quatD3Lift quatA quatC quatA_pow quatC_sq quatC_conj x)
      (quatD3Lift quatB quatD quatB_pow quatD_sq quatD_conj y) := by
  have hAB : Commute quatA quatB := by unfold Commute SemiconjBy; decide
  have hAD : Commute quatA quatD := by unfold Commute SemiconjBy; decide
  have hCB : Commute quatC quatB := by unfold Commute SemiconjBy; decide
  have hCD : Commute quatC quatD := by unfold Commute SemiconjBy; decide
  rcases x with i | i <;> rcases y with j | j
  · exact hAB.pow_pow _ _
  · exact (hAD.pow_left _).mul_right (hAB.pow_pow _ _)
  · exact (hCB.pow_right _).mul_left (hAB.pow_pow _ _)
  · exact ((hCD.mul_right (hCB.pow_right _)).mul_left
      ((hAD.pow_left _).mul_right (hAB.pow_pow _ _)))

@[expose] def quatD3Hom : DihedralGroup 3 × DihedralGroup 3 →* GL6 :=
  MonoidHom.noncommCoprod (quatD3Lift quatA quatC quatA_pow quatC_sq quatC_conj)
    (quatD3Lift quatB quatD quatB_pow quatD_sq quatD_conj) quatK_commute

@[expose] def s3s3Hom : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) →* GL6 :=
  quatD3Hom.comp (quatD3PermEquiv.symm.prodCongr quatD3PermEquiv.symm).toMonoidHom

theorem s3s3Hom_range : s3s3Hom.range = quatD3Hom.range := by
  rw [s3s3Hom, MonoidHom.range_comp, MonoidHom.range_eq_top.2
    (MulEquiv.surjective _), Subgroup.map_top]

theorem quatD3Hom_eq_one : ∀ p : DihedralGroup 3 × DihedralGroup 3, quatD3Hom p = 1 → p = 1 := by
  decide

theorem quatD3Hom_injective : Function.Injective quatD3Hom :=
  (injective_iff_map_eq_one _).2 quatD3Hom_eq_one

theorem s3s3Hom_injective : Function.Injective s3s3Hom :=
  quatD3Hom_injective.comp (MulEquiv.injective _)

theorem card_s3s3Hom_range : Nat.card ↥s3s3Hom.range = 36 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective s3s3Hom_injective).toEquiv, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem quat_d3_range_le {H : Subgroup GL6} (ha : quatA ∈ H) (hb : quatB ∈ H) (hc : quatC ∈ H)
    (hd : quatD ∈ H) : quatD3Hom.range ≤ H := by
  rintro _ ⟨⟨x, y⟩, rfl⟩
  have hX : ∀ x, quatD3Lift quatA quatC quatA_pow quatC_sq quatC_conj x ∈ H := by
    rintro (k | k)
    · exact H.pow_mem ha _
    · exact H.mul_mem hc (H.pow_mem ha _)
  have hY : ∀ y, quatD3Lift quatB quatD quatB_pow quatD_sq quatD_conj y ∈ H := by
    rintro (k | k)
    · exact H.pow_mem hb _
    · exact H.mul_mem hd (H.pow_mem hb _)
  exact H.mul_mem (hX x) (hY y)

theorem s3s3Hom_range_le : s3s3Hom.range ≤ M1Dot := by
  rw [s3s3Hom_range]
  exact quat_d3_range_le quatA_mem_M1Dot quatB_mem_M1Dot quatC_mem_M1Dot quatD_mem_M1Dot

theorem quat_conj_mem_normalizer {g : GL6} (h1 : g * quatLi * g⁻¹ ∈ q8Hom.range)
    (h2 : g * quatLj * g⁻¹ ∈ q8Hom.range) (h3 : g * quatRiInv * g⁻¹ ∈ q8Hom.range)
    (h4 : g * quatRjInv * g⁻¹ ∈ q8Hom.range) :
    g ∈ Subgroup.normalizer (q8Hom.range : Set GL6) := by
  have hle := quat_q8_range_le (H := q8Hom.range.comap (MulAut.conj g).toMonoidHom) h1 h2 h3 h4
  exact Subgroup.mem_normalizer_fintype fun n hn => hle hn

theorem quatA_mem_normalizer : quatA ∈ Subgroup.normalizer (q8Hom.range : Set GL6) :=
  quat_conj_mem_normalizer
    (MonoidHom.mem_range.2 ⟨(.xa 1, .a 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 1, .a 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .xa 3), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .a 1), by decide⟩)

theorem quatB_mem_normalizer : quatB ∈ Subgroup.normalizer (q8Hom.range : Set GL6) :=
  quat_conj_mem_normalizer
    (MonoidHom.mem_range.2 ⟨(.xa 0, .a 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.xa 1, .a 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .xa 3), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .a 1), by decide⟩)

theorem quatC_mem_normalizer : quatC ∈ Subgroup.normalizer (q8Hom.range : Set GL6) :=
  quat_conj_mem_normalizer
    (MonoidHom.mem_range.2 ⟨(.a 0, .xa 3), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .xa 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.xa 1, .a 0), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.xa 0, .a 0), by decide⟩)

theorem quatD_mem_normalizer : quatD ∈ Subgroup.normalizer (q8Hom.range : Set GL6) :=
  quat_conj_mem_normalizer
    (MonoidHom.mem_range.2 ⟨(.a 0, .a 3), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 0, .xa 2), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.a 1, .a 2), by decide⟩)
    (MonoidHom.mem_range.2 ⟨(.xa 0, .a 2), by decide⟩)

theorem s3s3Hom_range_le_normalizer :
    s3s3Hom.range ≤ Subgroup.normalizer (q8Hom.range : Set GL6) := by
  rw [s3s3Hom_range]
  exact quat_d3_range_le quatA_mem_normalizer quatB_mem_normalizer quatC_mem_normalizer
    quatD_mem_normalizer

@[expose] def quatFix56 : Subgroup GL6 :=
  MulAction.stabilizer GL6 x5 ⊓ MulAction.stabilizer GL6 x6

theorem quat_q8_range_le_fix : q8Hom.range ≤ quatFix56 := by
  have key : ∀ g : GL6, g • x5 = x5 → g • x6 = x6 → g ∈ quatFix56 := fun g h5 h6 =>
    Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 h5, MulAction.mem_stabilizer_iff.2 h6⟩
  exact quat_q8_range_le (key _ (by decide) (by decide)) (key _ (by decide) (by decide))
    (key _ (by decide) (by decide)) (key _ (by decide) (by decide))

theorem quatD3Hom_cube : ∀ p : DihedralGroup 3 × DihedralGroup 3,
    quatD3Hom p • x5 = x5 → quatD3Hom p • x6 = x6 → quatD3Hom p ^ 3 = 1 := by
  decide

theorem quatD3Hom_range_inf : quatD3Hom.range ⊓ q8Hom.range = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨p, rfl⟩, hgN⟩
  obtain ⟨h5, h6⟩ := Subgroup.mem_inf.1 (quat_q8_range_le_fix hgN)
  have h3 := quatD3Hom_cube p (MulAction.mem_stabilizer_iff.1 h5)
    (MulAction.mem_stabilizer_iff.1 h6)
  have h32 : quatD3Hom p ^ 32 = 1 := by
    have h := pow_card_eq_one' (G := ↥q8Hom.range) (x := ⟨quatD3Hom p, hgN⟩)
    rw [card_q8Hom_range] at h
    simpa using congrArg Subtype.val h
  have h1 := pow_gcd_eq_one.2 ⟨h3, h32⟩
  rw [show Nat.gcd 3 32 = 1 from by norm_num, pow_one] at h1
  rw [Subgroup.mem_bot, h1]

theorem s3s3Hom_range_inf : s3s3Hom.range ⊓ q8Hom.range = ⊥ := by
  rw [s3s3Hom_range]
  exact quatD3Hom_range_inf

@[expose] def quatProdMap : ↥q8Hom.range × ↥s3s3Hom.range → ↥M1Dot := fun p =>
  ⟨(p.1 : GL6) * p.2, M1Dot.mul_mem (q8Hom_range_le p.1.2) (s3s3Hom_range_le p.2.2)⟩

theorem quatProdMap_injective : Function.Injective quatProdMap := by
  rintro ⟨n, k⟩ ⟨n', k'⟩ h
  have h' : (n : GL6) * k = n' * k' := congrArg Subtype.val h
  have hmem : (n' : GL6)⁻¹ * n ∈ s3s3Hom.range ⊓ q8Hom.range := by
    refine Subgroup.mem_inf.2 ⟨?_, q8Hom.range.mul_mem (q8Hom.range.inv_mem n'.2) n.2⟩
    have : (n' : GL6)⁻¹ * n = k' * (k : GL6)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← h']
    rw [this]
    exact s3s3Hom.range.mul_mem k'.2 (s3s3Hom.range.inv_mem k.2)
  rw [s3s3Hom_range_inf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hn : n = n' := Subtype.ext hmem.symm
  subst hn
  have : (k : GL6) = k' := mul_left_cancel h'
  exact Prod.ext rfl (Subtype.ext this)

theorem card_quatProdMap_source : Nat.card (↥q8Hom.range × ↥s3s3Hom.range) = 1152 := by
  rw [Nat.card_prod, card_q8Hom_range, card_s3s3Hom_range]

theorem le_card_M1Dot : 1152 ≤ Nat.card ↥M1Dot := by
  rw [← card_quatProdMap_source]
  exact Nat.card_le_card_of_injective _ quatProdMap_injective

theorem quat_smul_def (g : GL6) (v : V6) : g • v = (g : M6) *ᵥ v :=
  rfl

theorem quat_mem_smul_iff (g : GL6) (S : Sub6) (m : V6) : m ∈ g • S ↔ ∃ b ∈ S, g • b = m :=
  Iff.rfl

theorem quat_mem_stabilizer_iff (g : GL6) (S : Sub6) :
    g ∈ MulAction.stabilizer GL6 S ↔ ∀ v : V6, v ∈ S ↔ g • v ∈ S := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h v
    constructor
    · intro hv
      have : g • v ∈ g • S := (quat_mem_smul_iff g S _).2 ⟨v, hv, rfl⟩
      rwa [h] at this
    · intro hv
      rw [← h] at hv
      obtain ⟨b, hb, hbv⟩ := (quat_mem_smul_iff g S _).1 hv
      have : b = v := MulAction.injective g hbv
      rwa [this] at hb
  · intro h
    ext m
    rw [quat_mem_smul_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (h b).1 hb
    · intro hm
      refine ⟨g⁻¹ • m, ?_, smul_inv_smul g m⟩
      exact (h (g⁻¹ • m)).2 (by rwa [smul_inv_smul])

theorem quat_mem_V4plus_iff (v : V6) : v ∈ V4plus ↔ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl | rfl <;> simp [x1, x2, x3, x4, xvec, Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]
    | smul c x _ hx => simp [hx.1, hx.2]
  · rintro ⟨h4, h5⟩
    have : v = v 0 • x1 + v 1 • x2 + v 2 • x3 + v 3 • x4 := by
      funext i
      fin_cases i <;> simp [x1, x2, x3, x4, xvec, Pi.single_apply, h4, h5]
    rw [this]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem quat_apply_xvec (A : M6) (i j : Fin 6) : (A *ᵥ xvec j) i = A i j := by
  rw [xvec, Matrix.mulVec_single_one]
  rfl

theorem quat_two_mul_eq_zero : ∀ a : ZMod 3, 2 * a = 0 → a = 0 := by decide

theorem quat_eJd (i : Fin 6) : eJd {0, 1, 2, 3} i = if i.val < 4 then -1 else 1 := by
  fin_cases i <;> rfl

theorem quat_zDot_apply (v : V6) (i : Fin 6) :
    (((zDot : GL6) : M6) *ᵥ v) i = if i.val < 4 then -v i else v i := by
  have h : ((zDot : GL6) : M6) = Matrix.diagonal (eJd {0, 1, 2, 3}) := rfl
  rw [h, Matrix.mulVec_diagonal, quat_eJd]
  split_ifs <;> simp

theorem quat_fwd {g : GL6} (hc : zDot * g = g * zDot) (v : V6) (hv : v 4 = 0 ∧ v 5 = 0) :
    ((g : M6) *ᵥ v) 4 = 0 ∧ ((g : M6) *ᵥ v) 5 = 0 := by
  have hz : ((zDot : GL6) : M6) *ᵥ v = -v := by
    funext i
    rw [quat_zDot_apply]
    fin_cases i <;> simp [hv.1, hv.2]
  have key : ((zDot : GL6) : M6) *ᵥ ((g : M6) *ᵥ v) = -((g : M6) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hc, Units.val_mul, ← Matrix.mulVec_mulVec, hz,
      Matrix.mulVec_neg]
  have h4 := congrFun key 4
  have h5 := congrFun key 5
  rw [quat_zDot_apply] at h4 h5
  have e4 : ¬ (4 : Fin 6).val < 4 := by decide
  have e5 : ¬ (5 : Fin 6).val < 4 := by decide
  rw [if_neg e4] at h4
  rw [if_neg e5] at h5
  refine ⟨quat_two_mul_eq_zero _ ?_, quat_two_mul_eq_zero _ ?_⟩
  · simp only [Pi.neg_apply] at h4
    linear_combination h4
  · simp only [Pi.neg_apply] at h5
    linear_combination h5

theorem quat_bil_xvec (u : V6) (j : Fin 6) (hj : j.val < 4) : bil u (xvec j) = 2 * u j := by
  fin_cases j <;> simp [bil_coord, xvec, Pi.single_apply] at hj ⊢ <;> ring

theorem quat_perp {g : GL6} (hg : g ∈ OVq)
    (hS : ∀ v : V6, (v 4 = 0 ∧ v 5 = 0) ↔ (((g : M6) *ᵥ v) 4 = 0 ∧ ((g : M6) *ᵥ v) 5 = 0))
    (p : V6) (hp : p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0 ∧ p 3 = 0) (j : Fin 6) (hj : j.val < 4) :
    ((g : M6) *ᵥ p) j = 0 := by
  have hgi : (g : M6) * ((g⁻¹ : GL6) : M6) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨w, hw⟩ : ∃ w : V6, w = ((g⁻¹ : GL6) : M6) *ᵥ xvec j := ⟨_, rfl⟩
  have hAw : (g : M6) *ᵥ w = xvec j := by
    rw [hw, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
  have hxj : (xvec j) 4 = 0 ∧ (xvec j) 5 = 0 := by
    fin_cases j <;> simp [xvec, Pi.single_apply] at hj ⊢
  have hw45 := (hS w).2 (by rw [hAw]; exact hxj)
  have h1 := bil_mulVec_of_mem_OVq hg p w
  have h2 : bil p w = 0 := by
    rw [bil_coord]
    simp [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hw45.1, hw45.2]
  rw [hAw, h2, quat_bil_xvec _ _ hj] at h1
  exact quat_two_mul_eq_zero _ h1

theorem quat_stab_iff {g : GL6} (hs : g ∈ MulAction.stabilizer GL6 V4plus) (v : V6) :
    (v 4 = 0 ∧ v 5 = 0) ↔ (((g : M6) *ᵥ v) 4 = 0 ∧ ((g : M6) *ᵥ v) 5 = 0) := by
  have := (quat_mem_stabilizer_iff g V4plus).1 hs v
  rwa [quat_mem_V4plus_iff, quat_smul_def, quat_mem_V4plus_iff] at this

theorem quat_commute_of_stab {g : GL6} (hg : g ∈ OVq) (hs : g ∈ MulAction.stabilizer GL6 V4plus) :
    zDot * g = g * zDot := by
  have hS := quat_stab_iff hs
  have F1 : ∀ i j : Fin 6, 4 ≤ i.val → j.val < 4 → (g : M6) i j = 0 := by
    intro i j hi hj
    have hxj : (xvec j) 4 = 0 ∧ (xvec j) 5 = 0 := by
      fin_cases j <;> simp [xvec, Pi.single_apply] at hj ⊢
    have h := (hS (xvec j)).1 hxj
    rw [← quat_apply_xvec (g : M6) i j]
    have hi' : i = 4 ∨ i = 5 := by
      revert hi
      fin_cases i <;> simp
    rcases hi' with rfl | rfl
    · exact h.1
    · exact h.2
  have F2 : ∀ i j : Fin 6, i.val < 4 → 4 ≤ j.val → (g : M6) i j = 0 := by
    intro i j hi hj
    have hxj : (xvec j) 0 = 0 ∧ (xvec j) 1 = 0 ∧ (xvec j) 2 = 0 ∧ (xvec j) 3 = 0 := by
      revert hj
      fin_cases j <;> simp [xvec, Pi.single_apply]
    rw [← quat_apply_xvec (g : M6) i j]
    exact quat_perp hg hS (xvec j) hxj i hi
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul]
  have hz : ((zDot : GL6) : M6) = Matrix.diagonal (eJd {0, 1, 2, 3}) := rfl
  rw [hz, Matrix.diagonal_mul, Matrix.mul_diagonal, quat_eJd, quat_eJd]
  by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
  · simp only [if_pos hi, if_pos hj]
    ring
  · have := F2 i j hi (by omega)
    simp [this]
  · have := F1 i j (by omega) hj
    simp [this]
  · simp only [if_neg hi, if_neg hj]
    ring

theorem M1Dot_eq_stab : M1Dot = MDot ⊓ MulAction.stabilizer GL6 V4plus := by
  ext g
  constructor
  · intro hg
    obtain ⟨hM, hc⟩ := Subgroup.mem_inf.1 hg
    have hcomm : zDot * g = g * zDot := Subgroup.mem_centralizer_iff.1 hc zDot rfl
    have hcomm' : zDot * g⁻¹ = g⁻¹ * zDot := (Commute.inv_right (show Commute zDot g from hcomm)).eq
    refine Subgroup.mem_inf.2 ⟨hM, (quat_mem_stabilizer_iff g V4plus).2 fun v => ?_⟩
    rw [quat_mem_V4plus_iff, quat_smul_def, quat_mem_V4plus_iff]
    refine ⟨quat_fwd hcomm v, fun h => ?_⟩
    have := quat_fwd hcomm' _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this
  · intro hg
    obtain ⟨hM, hs⟩ := Subgroup.mem_inf.1 hg
    exact quat_mem_M1Dot hM (quat_commute_of_stab (MDot_le_OVq hM) hs)

theorem quat_sq_sub_sq : ∀ a b : ZMod 3, a ^ 2 - b ^ 2 = -1 → a = 0 ∧ (b = 1 ∨ b = -1) := by
  decide

theorem quat_mulVec_x6 {g : GL6} (hg : g ∈ M1Dot) :
    (g : M6) *ᵥ x6 = x6 ∨ (g : M6) *ᵥ x6 = -x6 := by
  rw [M1Dot_eq_stab] at hg
  obtain ⟨hM, hs⟩ := Subgroup.mem_inf.1 hg
  have hS := quat_stab_iff hs
  have hq : qV ((g : M6) *ᵥ x6) = -1 :=
    (qV_mulVec_of_mem_OVq (MDot_le_OVq hM) x6).trans qV_x6
  have hx6 : x6 0 = 0 ∧ x6 1 = 0 ∧ x6 2 = 0 ∧ x6 3 = 0 := by
    simp [x6, xvec, Pi.single_apply]
  have h0 : ∀ j : Fin 6, j.val < 4 → ((g : M6) *ᵥ x6) j = 0 := fun j hj =>
    quat_perp (MDot_le_OVq hM) hS x6 hx6 j hj
  generalize (g : M6) *ᵥ x6 = w at hq h0 ⊢
  have e0 := h0 0 (by decide)
  have e1 := h0 1 (by decide)
  have e2 := h0 2 (by decide)
  have e3 := h0 3 (by decide)
  rw [qV, e0, e1, e2, e3] at hq
  obtain ⟨h4, h5⟩ := quat_sq_sub_sq (w 4) (w 5) (by linear_combination hq)
  rcases h5 with h5 | h5
  · left
    funext i
    fin_cases i <;> simp [x6, xvec, Pi.single_apply, e0, e1, e2, e3, h4, h5]
  · right
    funext i
    fin_cases i <;> simp [x6, xvec, Pi.single_apply, e0, e1, e2, e3, h4, h5]

theorem M1Dot_le_M0Dot : M1Dot ≤ M0Dot := by
  have hfwd : ∀ g ∈ M1Dot, ∀ v ∈ spn {x6}, g • v ∈ spn {x6} := by
    intro g hg v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [quat_smul_def, Matrix.mulVec_smul]
    rcases quat_mulVec_x6 hg with h | h
    · rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [h]
      exact Submodule.smul_mem _ _ (neg_mem (Submodule.subset_span rfl))
  intro g hg
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hg).1,
    (quat_mem_stabilizer_iff g _).2 fun v => ⟨fun hv => hfwd g hg v hv, fun hv => ?_⟩⟩
  have := hfwd g⁻¹ (M1Dot.inv_mem hg) _ hv
  rwa [inv_smul_smul] at this

theorem quat_card_step (H : Subgroup GL6) (x : V6) (X : Finset V6) (hX : ∀ h ∈ H, h • x ∈ X) :
    Nat.card ↥H ≤ X.card * Nat.card ↥(H ⊓ MulAction.stabilizer GL6 x) := by
  have h1 : Nat.card ↥H =
      Nat.card ↥(MulAction.orbit ↥H x) * Nat.card ↥(MulAction.stabilizer ↥H x) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H x)).symm
  have h2 : Nat.card ↥(MulAction.orbit ↥H x) ≤ X.card := by
    have := Nat.card_mono (Set.toFinite (X : Set V6))
      (show MulAction.orbit ↥H x ⊆ (X : Set V6) from by
        rintro _ ⟨h, rfl⟩
        exact hX h h.2)
    rw [Nat.card_coe_set_eq (MulAction.orbit ↥H x), Nat.card_coe_set_eq ((X : Set V6)),
      Set.ncard_coe_finset] at this
    rwa [Nat.card_coe_set_eq]
  have h3 : Nat.card ↥(MulAction.stabilizer ↥H x) =
      Nat.card ↥(H ⊓ MulAction.stabilizer GL6 x) :=
    Nat.card_congr
      { toFun := fun s => ⟨(s.1 : GL6), Subgroup.mem_inf.2 ⟨s.1.2, MulAction.mem_stabilizer_iff.2
          (MulAction.mem_stabilizer_iff.1 s.2)⟩⟩
        invFun := fun t => ⟨⟨t.1, (Subgroup.mem_inf.1 t.2).1⟩, MulAction.mem_stabilizer_iff.2
          (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 t.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, h3]
  exact Nat.mul_le_mul_right _ h2

@[expose] def quatX (S : List V6) : Finset V6 :=
  Finset.univ.filter fun v => v 4 = 0 ∧ v 5 = 0 ∧ qV v = 1 ∧ ∀ w ∈ S, bil v w = 0

set_option maxRecDepth 100000 in
theorem quatX_card0 : (quatX []).card = 24 := by decide
set_option maxRecDepth 100000 in
theorem quatX_card1 : (quatX [x1]).card = 6 := by decide
set_option maxRecDepth 100000 in
theorem quatX_card2 : (quatX [x1, x2]).card = 4 := by decide
set_option maxRecDepth 100000 in
theorem quatX_card3 : (quatX [x1, x2, x3]).card = 2 := by decide

theorem quat_M1Dot_mem {h : GL6} (hh : h ∈ M1Dot) {v : V6} (hv : v 4 = 0 ∧ v 5 = 0) :
    ((h : M6) *ᵥ v) 4 = 0 ∧ ((h : M6) *ᵥ v) 5 = 0 := by
  rw [M1Dot_eq_stab] at hh
  exact (quat_stab_iff (Subgroup.mem_inf.1 hh).2 v).1 hv

theorem quat_orbit_mem {h : GL6} (hh : h ∈ M1Dot) (S : List V6) (hfix : ∀ w ∈ S, h • w = w)
    {v : V6} (hv : v ∈ quatX S) : h • v ∈ quatX S := by
  simp only [quatX, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨h4, h5, hq, horth⟩ := hv
  have hOVq := MDot_le_OVq (Subgroup.mem_inf.1 hh).1
  have h45 := quat_M1Dot_mem hh ⟨h4, h5⟩
  refine ⟨h45.1, h45.2, ?_, ?_⟩
  · rw [quat_smul_def, qV_mulVec_of_mem_OVq hOVq]
    exact hq
  · intro w hw
    have hw' : (h : M6) *ᵥ w = w := hfix w hw
    rw [quat_smul_def]
    calc bil ((h : M6) *ᵥ v) w = bil ((h : M6) *ᵥ v) ((h : M6) *ᵥ w) := by rw [hw']
      _ = bil v w := bil_mulVec_of_mem_OVq hOVq v w
      _ = 0 := horth w hw

theorem quat_mulVec_x5 {g : GL6} (hg : g ∈ M1Dot) :
    (g : M6) *ᵥ x5 = x5 ∨ (g : M6) *ᵥ x5 = -x5 := by
  rw [M1Dot_eq_stab] at hg
  obtain ⟨hM, hs⟩ := Subgroup.mem_inf.1 hg
  have hS := quat_stab_iff hs
  have hq : qV ((g : M6) *ᵥ x5) = 1 :=
    (qV_mulVec_of_mem_OVq (MDot_le_OVq hM) x5).trans (by decide)
  have hx5 : x5 0 = 0 ∧ x5 1 = 0 ∧ x5 2 = 0 ∧ x5 3 = 0 := by
    simp [x5, xvec, Pi.single_apply]
  have h0 : ∀ j : Fin 6, j.val < 4 → ((g : M6) *ᵥ x5) j = 0 := fun j hj =>
    quat_perp (MDot_le_OVq hM) hS x5 hx5 j hj
  generalize (g : M6) *ᵥ x5 = w at hq h0 ⊢
  have e0 := h0 0 (by decide)
  have e1 := h0 1 (by decide)
  have e2 := h0 2 (by decide)
  have e3 := h0 3 (by decide)
  rw [qV, e0, e1, e2, e3] at hq
  have key : ∀ a b : ZMod 3, a ^ 2 - b ^ 2 = 1 → b = 0 ∧ (a = 1 ∨ a = -1) := by decide
  obtain ⟨h5, h4⟩ := key (w 4) (w 5) (by linear_combination hq)
  rcases h4 with h4 | h4
  · left
    funext i
    fin_cases i <;> simp [x5, xvec, Pi.single_apply, e0, e1, e2, e3, h4, h5]
  · right
    funext i
    fin_cases i <;> simp [x5, xvec, Pi.single_apply, e0, e1, e2, e3, h4, h5]

theorem quat_matrix_eq {A B : M6} (h : ∀ j, A *ᵥ xvec j = B *ᵥ xvec j) : A = B :=
  Matrix.ext fun i j => by rw [← quat_apply_xvec A i j, ← quat_apply_xvec B i j, h j]

theorem quat_matrix_eq_of_cols {A B : M6} (h0 : A *ᵥ xvec 0 = B *ᵥ xvec 0)
    (h1 : A *ᵥ xvec 1 = B *ᵥ xvec 1) (h2 : A *ᵥ xvec 2 = B *ᵥ xvec 2)
    (h3 : A *ᵥ xvec 3 = B *ᵥ xvec 3) (h4 : A *ᵥ xvec 4 = B *ᵥ xvec 4)
    (h5 : A *ᵥ xvec 5 = B *ᵥ xvec 5) : A = B :=
  quat_matrix_eq fun j => by fin_cases j <;> assumption

theorem quat_mem_MDot_iff_of_refl (l : List ReflVec) (g : GL6)
    (hg : (g : M6) = (l.map quatReflMat).prod) :
    g ∈ MDot ↔ Even l.length ∧ Even (l.countP fun v => qV v.1 = -1) := by
  have : g = (l.map reflOf).prod := Units.ext (by rw [hg, quat_val_prod_refl])
  rw [this, prod_refl_mem_MDot_iff]

theorem quat_eq_one_of_fix {h : GL6} (hh : h ∈ M1Dot) (f1 : (h : M6) *ᵥ x1 = x1)
    (f2 : (h : M6) *ᵥ x2 = x2) (f3 : (h : M6) *ᵥ x3 = x3) (f4 : (h : M6) *ᵥ x4 = x4) :
    h = 1 := by
  have hMD := (Subgroup.mem_inf.1 hh).1
  have c0 : (h : M6) *ᵥ xvec 0 = xvec 0 := f1
  have c1 : (h : M6) *ᵥ xvec 1 = xvec 1 := f2
  have c2 : (h : M6) *ᵥ xvec 2 = xvec 2 := f3
  have c3 : (h : M6) *ᵥ xvec 3 = xvec 3 := f4
  have key : ∀ (a b : ZMod 3) (l : List ReflVec),
      (Matrix.diagonal ![1, 1, 1, 1, a, b] : M6) = (l.map quatReflMat).prod →
      (h : M6) *ᵥ x5 = a • x5 → (h : M6) *ᵥ x6 = b • x6 →
      ¬ (Even l.length ∧ Even (l.countP fun v => qV v.1 = -1)) → False := by
    intro a b l hl c4 c5 hnot
    have c4' : (h : M6) *ᵥ xvec 4 = a • xvec 4 := c4
    have c5' : (h : M6) *ᵥ xvec 5 = b • xvec 5 := c5
    have hcol : ∀ (j : Fin 6) (c : ZMod 3), (h : M6) *ᵥ xvec j = c • xvec j →
        c = (![1, 1, 1, 1, a, b] : Fin 6 → ZMod 3) j →
        (h : M6) *ᵥ xvec j = (Matrix.diagonal ![1, 1, 1, 1, a, b] : M6) *ᵥ xvec j := by
      intro j c hc hcj
      rw [hc, hcj]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hij : i = j
      · subst hij
        simp [xvec]
      · simp [xvec, Pi.single_apply, hij]
    have hM : (h : M6) = Matrix.diagonal ![1, 1, 1, 1, a, b] :=
      quat_matrix_eq_of_cols (hcol 0 1 (by rw [one_smul]; exact c0) rfl)
        (hcol 1 1 (by rw [one_smul]; exact c1) rfl) (hcol 2 1 (by rw [one_smul]; exact c2) rfl)
        (hcol 3 1 (by rw [one_smul]; exact c3) rfl) (hcol 4 a c4' rfl) (hcol 5 b c5' rfl)
    exact hnot ((quat_mem_MDot_iff_of_refl l h (hM.trans hl)).1 hMD)
  rcases quat_mulVec_x5 hh with c4 | c4 <;> rcases quat_mulVec_x6 hh with c5 | c5
  · apply Units.ext
    rw [Units.val_one]
    exact quat_matrix_eq_of_cols (by rw [c0, Matrix.one_mulVec]) (by rw [c1, Matrix.one_mulVec])
      (by rw [c2, Matrix.one_mulVec]) (by rw [c3, Matrix.one_mulVec])
      (by rw [show xvec 4 = x5 from rfl, c4, Matrix.one_mulVec])
      (by rw [show xvec 5 = x6 from rfl, c5, Matrix.one_mulVec])
  · exact (key 1 (-1) [quatRV ![0, 0, 0, 0, 0, 1]] (by decide) (by rw [one_smul]; exact c4)
      (by rw [neg_one_smul]; exact c5) (by decide)).elim
  · exact (key (-1) 1 [quatRV ![0, 0, 0, 0, 1, 0]] (by decide) (by rw [neg_one_smul]; exact c4)
      (by rw [one_smul]; exact c5) (by decide)).elim
  · exact (key (-1) (-1) [quatRV ![0, 0, 0, 0, 1, 0], quatRV ![0, 0, 0, 0, 0, 1]] (by decide)
      (by rw [neg_one_smul]; exact c4) (by rw [neg_one_smul]; exact c5) (by decide)).elim

@[expose] def quatF1 : Subgroup GL6 := M1Dot ⊓ MulAction.stabilizer GL6 x1

@[expose] def quatF2 : Subgroup GL6 := quatF1 ⊓ MulAction.stabilizer GL6 x2

@[expose] def quatF3 : Subgroup GL6 := quatF2 ⊓ MulAction.stabilizer GL6 x3

@[expose] def quatF4 : Subgroup GL6 := quatF3 ⊓ MulAction.stabilizer GL6 x4

theorem quatF1_le : quatF1 ≤ M1Dot := inf_le_left

theorem quatF2_le : quatF2 ≤ M1Dot := inf_le_left.trans quatF1_le

theorem quatF3_le : quatF3 ≤ M1Dot := inf_le_left.trans quatF2_le

theorem quat_fix_of_mem_stab {h : GL6} {x : V6} (hh : h ∈ MulAction.stabilizer GL6 x) :
    (h : M6) *ᵥ x = x :=
  MulAction.mem_stabilizer_iff.1 hh

theorem quatF4_eq_bot : quatF4 = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  obtain ⟨hh3, h4⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hh2, h3⟩ := Subgroup.mem_inf.1 hh3
  obtain ⟨hh1, h2⟩ := Subgroup.mem_inf.1 hh2
  obtain ⟨hM, h1⟩ := Subgroup.mem_inf.1 hh1
  exact quat_eq_one_of_fix hM (quat_fix_of_mem_stab h1) (quat_fix_of_mem_stab h2)
    (quat_fix_of_mem_stab h3) (quat_fix_of_mem_stab h4)

set_option maxRecDepth 100000 in
theorem card_M1Dot_le : Nat.card ↥M1Dot ≤ 1152 := by
  have s0 := quat_card_step M1Dot x1 (quatX []) fun h hh =>
    quat_orbit_mem hh [] (by simp) (by
      simp only [quatX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  have s1 := quat_card_step quatF1 x2 (quatX [x1]) fun h hh =>
    quat_orbit_mem (quatF1_le hh) [x1] (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2)) (by
      simp only [quatX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  have s2 := quat_card_step quatF2 x3 (quatX [x1, x2]) fun h hh =>
    quat_orbit_mem (quatF2_le hh) [x1, x2] (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
      · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2) (by
      simp only [quatX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  have s3 := quat_card_step quatF3 x4 (quatX [x1, x2, x3]) fun h hh =>
    quat_orbit_mem (quatF3_le hh) [x1, x2, x3] (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact MulAction.mem_stabilizer_iff.1
          (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1).2
      · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
      · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2) (by
      simp only [quatX, Finset.mem_filter, Finset.mem_univ, true_and]; decide)
  rw [quatX_card0] at s0
  rw [quatX_card1] at s1
  rw [quatX_card2] at s2
  rw [quatX_card3] at s3
  have s4 : Nat.card ↥quatF4 = 1 := by
    rw [quatF4_eq_bot]
    exact Subgroup.card_bot
  calc Nat.card ↥M1Dot ≤ 24 * Nat.card ↥quatF1 := s0
    _ ≤ 24 * (6 * Nat.card ↥quatF2) := Nat.mul_le_mul_left _ s1
    _ ≤ 24 * (6 * (4 * Nat.card ↥quatF3)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s2)
    _ ≤ 24 * (6 * (4 * (2 * Nat.card ↥quatF4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ s3))
    _ = 1152 := by rw [s4]

theorem card_M1Dot : Nat.card ↥M1Dot = 1152 :=
  le_antisymm card_M1Dot_le le_card_M1Dot

theorem quatProdMap_bijective : Function.Bijective quatProdMap :=
  quatProdMap_injective.bijective_of_nat_card_le (by rw [card_M1Dot, card_quatProdMap_source])

theorem quat_exists_mul {x : GL6} (hx : x ∈ M1Dot) :
    ∃ n ∈ q8Hom.range, ∃ k ∈ s3s3Hom.range, x = n * k := by
  obtain ⟨⟨n, k⟩, h⟩ := quatProdMap_bijective.2 ⟨x, hx⟩
  exact ⟨n, n.2, k, k.2, (congrArg Subtype.val h).symm⟩

theorem q8Hom_range_sup : q8Hom.range ⊔ s3s3Hom.range = M1Dot := by
  apply le_antisymm
  · exact sup_le q8Hom_range_le s3s3Hom_range_le
  · intro x hx
    obtain ⟨n, hn, k, hk, rfl⟩ := quat_exists_mul hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hk)

theorem quat_normalizer_M1Dot :
    M1Dot ≤ Subgroup.normalizer (q8Hom.range : Set GL6) := by
  rw [← q8Hom_range_sup]
  exact sup_le Subgroup.le_normalizer s3s3Hom_range_le_normalizer

theorem quat_mem_Q1Dot {x : GL6} :
    x ∈ Q1Dot ↔ ∃ y : ↥M1Dot, y ∈ CFSG.pCore 2 ↥M1Dot ∧ (y : GL6) = x :=
  Subgroup.mem_map

theorem q8Hom_range_le_Q1Dot : q8Hom.range ≤ Q1Dot := by
  have hnorm : (q8Hom.range.subgroupOf M1Dot).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (quat_normalizer_M1Dot g.2) n).1 hn
  have hpgp : IsPGroup 2 (q8Hom.range.subgroupOf M1Dot) := by
    refine IsPGroup.of_card (n := 5) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe q8Hom_range_le).toEquiv,
      card_q8Hom_range]
    norm_num
  have hle : q8Hom.range.subgroupOf M1Dot ≤ CFSG.pCore 2 ↥M1Dot := le_sSup ⟨hnorm, hpgp⟩
  intro x hx
  exact quat_mem_Q1Dot.2 ⟨⟨x, q8Hom_range_le hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem quat_Q1Dot_pow {x : GL6} (hx : x ∈ Q1Dot) : ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨y, hy, rfl⟩ := quat_mem_Q1Dot.1 hx
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M1Dot)) ⟨y, hy⟩
  refine ⟨m, ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥M1Dot) => ((z : ↥M1Dot) : GL6)) hm
  simpa using this

theorem quat_Q1Dot_conj {g : GL6} (hg : g ∈ M1Dot) {r : GL6} (hr : r ∈ Q1Dot) :
    g * r * g⁻¹ ∈ Q1Dot := by
  obtain ⟨y, hy, rfl⟩ := quat_mem_Q1Dot.1 hr
  have h1 : (⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ : ↥M1Dot) ∈ CFSG.pCore 2 ↥M1Dot :=
    (CFSG.pCore_normal (p := 2) (G := ↥M1Dot)).conj_mem y hy ⟨g, hg⟩
  have h2 : ((⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ : ↥M1Dot) : GL6) = g * (y : GL6) * g⁻¹ := by
    simp
  rw [← h2]
  exact quat_mem_Q1Dot.2 ⟨_, h1, rfl⟩

theorem quatD3_comm_cube : ∀ a b : DihedralGroup 3 × DihedralGroup 3,
    (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := by
  decide

theorem quatD3_center : ∀ a : DihedralGroup 3 × DihedralGroup 3,
    (∀ b, a * b * a⁻¹ * b⁻¹ = 1) → a = 1 := by
  decide

theorem quat_d3_normal_two_group {K : Type*} [Group K] (f : DihedralGroup 3 × DihedralGroup 3 →* K)
    (hf : Function.Injective f) (Q : Subgroup K) (hQ : ∀ x ∈ Q, ∃ m : ℕ, x ^ (2 ^ m) = 1)
    (hnorm : ∀ t, ∀ r ∈ Q, f t * r * (f t)⁻¹ ∈ Q) (p : DihedralGroup 3 × DihedralGroup 3)
    (hp : f p ∈ Q) : p = 1 := by
  have hcomm : ∀ t, p * t * p⁻¹ * t⁻¹ = 1 := by
    intro t
    refine hf ?_
    rw [map_one]
    have hcQ : f (p * t * p⁻¹ * t⁻¹) ∈ Q := by
      have h1 := hnorm t (f p)⁻¹ (Q.inv_mem hp)
      have h2 := Q.mul_mem hp h1
      simpa [map_mul, map_inv, mul_assoc] using h2
    have hc3 : f (p * t * p⁻¹ * t⁻¹) ^ 3 = 1 := by
      rw [← map_pow, quatD3_comm_cube, map_one]
    obtain ⟨m, hm⟩ := hQ _ hcQ
    have h := pow_gcd_eq_one.2 ⟨hc3, hm⟩
    rw [(Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2) : Nat.Coprime 3 (2 ^ m)),
      pow_one] at h
    exact h
  exact quatD3_center p hcomm

theorem Q1Dot_eq : Q1Dot = q8Hom.range := by
  refine le_antisymm ?_ q8Hom_range_le_Q1Dot
  intro p hp
  have hpM : p ∈ M1Dot := by
    obtain ⟨y, _, rfl⟩ := quat_mem_Q1Dot.1 hp
    exact y.2
  obtain ⟨n, hn, k, hk, rfl⟩ := quat_exists_mul hpM
  have hnQ : n ∈ Q1Dot := q8Hom_range_le_Q1Dot hn
  have hkQ : k ∈ Q1Dot := by
    have := Q1Dot.mul_mem (Q1Dot.inv_mem hnQ) hp
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  rw [s3s3Hom_range] at hk
  obtain ⟨p, rfl⟩ := hk
  have hK : p = 1 :=
    quat_d3_normal_two_group quatD3Hom quatD3Hom_injective Q1Dot (fun x hx => quat_Q1Dot_pow hx)
      (fun t r hr => quat_Q1Dot_conj
        (s3s3Hom_range_le (by rw [s3s3Hom_range]; exact ⟨t, rfl⟩)) hr) p hkQ
  rw [hK, map_one, mul_one]
  exact hn

@[expose] def Q1DotEquiv : ↥Q1Dot ≃* Q8Sq :=
  (MulEquiv.subgroupCongr Q1Dot_eq).trans
    ((QuotientGroup.quotientKerEquivRange q8Hom).symm.trans
      (QuotientGroup.quotientMulEquivOfEq q8Hom_ker))

theorem zDot_mem_Q1Dot : zDot ∈ Q1Dot := by
  rw [Q1Dot_eq]
  exact zDot_mem_q8Hom_range

theorem M1Dot_structure :
    Nonempty (↥Q1Dot ≃* Q8Sq) ∧
      ∃ K : Subgroup GL6, K ≤ M1Dot ∧ K ⊓ Q1Dot = ⊥ ∧ Q1Dot ⊔ K = M1Dot ∧
        Nonempty (↥K ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  ⟨⟨Q1DotEquiv⟩, s3s3Hom.range, s3s3Hom_range_le, by rw [Q1Dot_eq, s3s3Hom_range_inf],
    by rw [Q1Dot_eq, q8Hom_range_sup], ⟨(MonoidHom.ofInjective s3s3Hom_injective).symm⟩⟩

end

end CFSG.Quasithin.SimsF5
