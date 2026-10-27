module

public import CFSG.OddTranspositions.F25Group
public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.OddTranspositions.O4PairF25Model
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])


@[expose] def X0 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 0⟩, ⟨0, 1⟩; ⟨0, 3⟩, ⟨0, 0⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X1 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 0⟩, ⟨0, 2⟩; ⟨0, 4⟩, ⟨0, 0⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X2 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨0, 1⟩; ⟨0, 2⟩, ⟨0, 4⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X3 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨0, 2⟩; ⟨0, 1⟩, ⟨0, 4⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X4 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨0, 3⟩; ⟨0, 4⟩, ⟨0, 4⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X5 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨0, 4⟩; ⟨0, 3⟩, ⟨0, 4⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X6 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 2⟩, ⟨0, 1⟩; ⟨0, 4⟩, ⟨0, 3⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X7 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 2⟩, ⟨0, 2⟩; ⟨0, 2⟩, ⟨0, 3⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X8 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 2⟩, ⟨0, 3⟩; ⟨0, 3⟩, ⟨0, 3⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X9 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 2⟩, ⟨0, 4⟩; ⟨0, 1⟩, ⟨0, 3⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def X (i : Fin 10) : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ![X0, X1, X2, X3, X4, X5, X6, X7, X8, X9] i

@[expose] def P0 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨2, 0⟩; ⟨1, 0⟩, ⟨0, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P1 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨2, 0⟩, ⟨0, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P2 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨2, 0⟩; ⟨1, 4⟩, ⟨3, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P3 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨2, 2⟩, ⟨2, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P4 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨2, 3⟩, ⟨3, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P5 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨2, 0⟩; ⟨1, 1⟩, ⟨2, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P6 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨2, 0⟩; ⟨1, 3⟩, ⟨1, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P7 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨2, 4⟩, ⟨4, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P8 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨2, 1⟩, ⟨1, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P9 : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨2, 0⟩; ⟨1, 2⟩, ⟨4, 1⟩], by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    apply F25t.ext <;>
      simp [mul25_def, add25_def, neg25_def, one25_def] <;>
      decide⟩

@[expose] def P (i : Fin 10) : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ![P0, P1, P2, P3, P4, P5, P6, P7, P8, P9] i

@[expose] def x (i : Fin 10) : PSL2 F25t :=
  CFSG.PSL2Table.mk (X i)

private def frob25tExplicit : F25t ≃+* F25t where
  toFun x := ⟨x.a, -x.b⟩
  invFun x := ⟨x.a, -x.b⟩
  left_inv x := by
    cases x with
    | mk a b =>
      apply F25t.ext
      · rfl
      · simp [neg_neg]
  right_inv x := by
    cases x with
    | mk a b =>
      apply F25t.ext
      · rfl
      · simp [neg_neg]
  map_add' x y := by
    cases x with
    | mk a b =>
      cases y with
      | mk c d =>
        apply F25t.ext <;> simp [add25_def, neg25_def] <;> ring
  map_mul' x y := by
    cases x with
    | mk a b =>
      cases y with
      | mk c d =>
        apply F25t.ext <;> simp [mul25_def, neg25_def] <;> ring

private theorem frob25tExplicit_ne_one : frob25tExplicit ≠ 1 := by
  intro h
  have h1 := congrArg (fun e : F25t ≃+* F25t => e ⟨0, 1⟩) h
  simp [frob25tExplicit] at h1
  letI : DecidableEq F25t := f25tDecEq
  exact absurd h1 (by decide)

private theorem frob25t_eq_frob25tExplicit : frob25t = frob25tExplicit := by
  obtain ⟨z, hz_ne, hz_unique⟩ :=
    (Nat.card_eq_two_iff' (1 : F25t ≃+* F25t)).mp card_ringAut_F25t
  rw [hz_unique frob25t frob25t_ne_one, hz_unique frob25tExplicit frob25tExplicit_ne_one]

macro "matrix_ext" : tactic =>
  `(tactic|
    (apply Matrix.SpecialLinearGroup.ext
     intro a b
     fin_cases a <;> fin_cases b <;>
     apply F25t.ext <;>
     simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
       CFSG.PSL2Table.coe_inv_SL, Matrix.SpecialLinearGroup.map_apply_coe,
       Matrix.mul_apply, Fin.sum_univ_two, frob25tExplicit,
       P, P0, P1, P2, P3, P4, P5, P6, P7, P8, P9,
       X, X0, X1, X2, X3, X4, X5, X6, X7, X8, X9,
       mul25_def, add25_def, neg25_def, one25_def] <;>
     decide))

theorem x_in_twisted_class (i : Fin 10) :
    CFSG.PSL2Table.mk (X i) =
      CFSG.PSL2Table.mk
        (P i * (Matrix.SpecialLinearGroup.map frob25t.toRingHom (P i))⁻¹) := by
  rw [frob25t_eq_frob25tExplicit, CFSG.PSL2Table.mk_eq_mk_iff]
  fin_cases i
  · left; matrix_ext
  · right; matrix_ext
  · left; matrix_ext
  · right; matrix_ext
  · left; matrix_ext
  · right; matrix_ext
  · left; matrix_ext
  · right; matrix_ext
  · left; matrix_ext
  · right; matrix_ext

theorem x_fixed (i : Fin 10) :
    CFSG.GorensteinWalter.psl2FieldAut F25t frob25t (x i) = x i := by
  rw [frob25t_eq_frob25tExplicit]
  change CFSG.GorensteinWalter.psl2FieldAut F25t frob25tExplicit (CFSG.PSL2Table.mk (X i)) =
    CFSG.PSL2Table.mk (X i)
  rw [CFSG.GorensteinWalter.psl2FieldAut_apply]
  have hmk : CFSG.GorensteinWalter.psl2RingEquiv frob25tExplicit
        (CFSG.PSL2Table.mk (X i)) =
      CFSG.PSL2Table.mk
        (Matrix.SpecialLinearGroup.map frob25tExplicit.toRingHom (X i)) := by
    simpa only [CFSG.PSL2Table.mk] using
      (CFSG.GorensteinWalter.psl2RingEquiv_mk frob25tExplicit (X i))
  have h : Matrix.SpecialLinearGroup.map frob25tExplicit.toRingHom (X i) = -(X i) := by
    fin_cases i <;> matrix_ext
  rw [hmk, h, CFSG.PSL2Table.mk_neg]

theorem X_eq_or_neg_eq_imp_eq (i j : Fin 10) :
    (X j = X i ∨ X j = -X i) → i = j := by
  letI : DecidableEq F25t := f25tDecEq
  fin_cases i <;> fin_cases j <;> decide

theorem x_injective : Function.Injective x := by
  intro i j hij
  change CFSG.PSL2Table.mk (X i) = CFSG.PSL2Table.mk (X j) at hij
  exact X_eq_or_neg_eq_imp_eq i j ((CFSG.PSL2Table.mk_eq_mk_iff (X i) (X j)).mp hij)

theorem X_mul_pow_eq_pm_one (i j : Fin 10) :
    X i * X j = 1 ∨ X i * X j = -1 ∨
      X i * X j * (X i * X j) = 1 ∨ X i * X j * (X i * X j) = -1 ∨
      X i * X j * (X i * X j) * (X i * X j) = 1 ∨
      X i * X j * (X i * X j) * (X i * X j) = -1 := by
  letI : DecidableEq F25t := f25tDecEq
  fin_cases i <;> fin_cases j <;> decide

theorem orderOf_mk_mem_of_pow_eq_pm_one {M : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (h : M = 1 ∨ M = -1 ∨ M * M = 1 ∨ M * M = -1 ∨ M * M * M = 1 ∨ M * M * M = -1) :
    orderOf (CFSG.PSL2Table.mk M) ∈ ({1, 2, 3} : Set ℕ) := by
  rcases h with h | h | h | h | h | h
  · rw [h, map_one]
    simp
  · rw [h, CFSG.PSL2Table.mk_neg, map_one]
    simp
  · have h2 : CFSG.PSL2Table.mk M ^ 2 = 1 := by
      rw [pow_two, ← map_mul, h, map_one]
    have hd : orderOf (CFSG.PSL2Table.mk M) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1 <;> rw [h1] <;> simp
  · have h2 : CFSG.PSL2Table.mk M ^ 2 = 1 := by
      rw [pow_two, ← map_mul, h, CFSG.PSL2Table.mk_neg, map_one]
    have hd : orderOf (CFSG.PSL2Table.mk M) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1 <;> rw [h1] <;> simp
  · have h3 : CFSG.PSL2Table.mk M ^ 3 = 1 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      rw [← map_mul, ← map_mul, h, map_one]
    have hd : orderOf (CFSG.PSL2Table.mk M) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> simp
  · have h3 : CFSG.PSL2Table.mk M ^ 3 = 1 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      rw [← map_mul, ← map_mul, h, CFSG.PSL2Table.mk_neg, map_one]
    have hd : orderOf (CFSG.PSL2Table.mk M) ∣ 3 :=
      orderOf_dvd_iff_pow_eq_one.mpr h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> simp

theorem ten_products_order :
    ∀ i j : Fin 10, orderOf (x i * x j) ∈ ({1, 2, 3} : Set ℕ) := by
  intro i j
  have hmul : x i * x j = CFSG.PSL2Table.mk (X i * X j) := by
    simp [x, map_mul]
  rw [hmul]
  exact orderOf_mk_mem_of_pow_eq_pm_one (X_mul_pow_eq_pm_one i j)

end CFSG.OddTranspositions.QZ
