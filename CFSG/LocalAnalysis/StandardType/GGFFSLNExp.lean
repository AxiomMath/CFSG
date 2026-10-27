module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

private theorem inv_eq_sq_of_pow_three {G : Type*} [Group G] {w : G} (h : w ^ 3 = 1) :
    w⁻¹ = w ^ 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ']
  simpa using h

private theorem inv_sq_eq_self_of_pow_three {G : Type*} [Group G] {w : G} (h : w ^ 3 = 1) :
    (w ^ 2)⁻¹ = w := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ]
  simpa using h

private theorem cjp_eq_mul_pow_sub {G : Type} [Group G] {w : G} (h : w ^ 3 = 1)
    (a : Fin 3) (u : G) : cjp w a u = w ^ (a : ℕ) * u * w ^ (3 - (a : ℕ)) := by
  unfold cjp
  fin_cases a <;> simp [h, inv_eq_sq_of_pow_three h, inv_sq_eq_self_of_pow_three h]

private theorem rootRel_of_mul_pow {G : Type} [Group G] {w u : G} (h : w ^ 3 = 1)
    (hu : u * (w * u * w ^ 2) = w ^ 2 * u * w) : RootRel w u := by
  unfold RootRel
  rw [inv_eq_sq_of_pow_three h, inv_sq_eq_self_of_pow_three h]
  exact hu

private def c6R0M : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![!![1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 1, 1, 0, 0;
      0, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1]]

private theorem c6R0M_sq (a : Fin 3) : c6R0M a * c6R0M a = 1 := by
  fin_cases a <;> decide +kernel

private def c6R0 (a : Fin 3) : SL(6, ZMod 2) :=
  W6.mkSL6 (c6R0M a) (c6R0M a) (c6R0M_sq a)

private theorem cjp_c6R0 (a : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r 0) = c6R0 a := by
  change cjp (W6.T 0) a (N6.r 0) = c6R0 a
  rw [cjp_eq_mul_pow_sub (W6.pow_T 0)]
  fin_cases a <;> decide +kernel

private def c6R0'M : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0;
      0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0;
      1, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0;
      1, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1]]

private theorem c6R0'M_sq (a : Fin 3) : c6R0'M a * c6R0'M a = 1 := by
  fin_cases a <;> decide +kernel

private def c6R0' (a : Fin 3) : SL(6, ZMod 2) :=
  W6.mkSL6 (c6R0'M a) (c6R0'M a) (c6R0'M_sq a)

private theorem cjp_c6R0' (a : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r' 0) = c6R0' a := by
  change cjp (W6.T 0) a (N6.r' 0) = c6R0' a
  rw [cjp_eq_mul_pow_sub (W6.pow_T 0)]
  fin_cases a <;> decide +kernel

private def c6R1M : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 1;
      0, 0, 0, 1, 1, 1;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 1;
      0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 1]]

private theorem c6R1M_sq (a : Fin 3) : c6R1M a * c6R1M a = 1 := by
  fin_cases a <;> decide +kernel

private def c6R1 (a : Fin 3) : SL(6, ZMod 2) :=
  W6.mkSL6 (c6R1M a) (c6R1M a) (c6R1M_sq a)

private theorem cjp_c6R1 (a : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r 1) = c6R1 a := by
  change cjp (W6.T 1) a (N6.r 1) = c6R1 a
  rw [cjp_eq_mul_pow_sub (W6.pow_T 1)]
  fin_cases a <;> decide +kernel

private def c6R1'M : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 1, 0, 1, 0;
      0, 0, 0, 1, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 1, 1, 1, 0;
      0, 0, 1, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 1, 1, 0;
      0, 0, 1, 1, 0, 1]]

private theorem c6R1'M_sq (a : Fin 3) : c6R1'M a * c6R1'M a = 1 := by
  fin_cases a <;> decide +kernel

private def c6R1' (a : Fin 3) : SL(6, ZMod 2) :=
  W6.mkSL6 (c6R1'M a) (c6R1'M a) (c6R1'M_sq a)

private theorem cjp_c6R1' (a : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r' 1) = c6R1' a := by
  change cjp (W6.T 1) a (N6.r' 1) = c6R1' a
  rw [cjp_eq_mul_pow_sub (W6.pow_T 1)]
  fin_cases a <;> decide +kernel


theorem pi_z_SL6 : ∀ i, W6.tw * W6.T i * W6.tw⁻¹ = W6.T (finRotate 3 i) := by
  intro i
  fin_cases i
  · simpa using W6.conj0_T
  · simpa using W6.conj1_T
  · simpa using W6.conj2_T

theorem x0_z0_SL6 : N6.x0 * W6.T 0 * N6.x0⁻¹ = W6.T 0 := by
  have h : N6.x0 * W6.T 0 = W6.T 0 * N6.x0 := by decide +kernel
  rw [h]
  group

theorem x0_z1_SL6 : N6.x0 * W6.T 1 * N6.x0⁻¹ = W6.T 2 := by
  have h : N6.x0 * W6.T 1 = W6.T 2 * N6.x0 := by decide +kernel
  rw [h]
  group

theorem x0_z2_SL6 : N6.x0 * W6.T 2 * N6.x0⁻¹ = W6.T 1 := by
  have h : N6.x0 * W6.T 2 = W6.T 1 * N6.x0 := by decide +kernel
  rw [h]
  group

theorem root_sq_SL6 : ∀ j, N6.r j * N6.r j = 1 ∧ N6.r' j * N6.r' j = 1 := by
  decide +kernel

theorem root_comm_SL6 : ∀ j, N6.r j * rootK₁ W6.T j = rootK₁ W6.T j * N6.r j ∧
    N6.r j * rootK₂ W6.T j = rootK₂ W6.T j * N6.r j ∧
    N6.r' j * rootK₁ W6.T j = rootK₁ W6.T j * N6.r' j ∧
    N6.r' j * rootK₂ W6.T j = rootK₂ W6.T j * N6.r' j := by
  decide +kernel

theorem root_rel_SL6 : ∀ j, RootRel (rootW W6.T j) (N6.r j) ∧ RootRel (rootW W6.T j) (N6.r' j) := by
  intro j
  fin_cases j
  · have h3 : rootW W6.T 0 ^ 3 = 1 := by decide +kernel
    have h : N6.r 0 * (rootW W6.T 0 * N6.r 0 * rootW W6.T 0 ^ 2) =
        rootW W6.T 0 ^ 2 * N6.r 0 * rootW W6.T 0 := by decide +kernel
    have h' : N6.r' 0 * (rootW W6.T 0 * N6.r' 0 * rootW W6.T 0 ^ 2) =
        rootW W6.T 0 ^ 2 * N6.r' 0 * rootW W6.T 0 := by decide +kernel
    exact ⟨rootRel_of_mul_pow (u := N6.r 0) h3 h,
      rootRel_of_mul_pow (u := N6.r' 0) h3 h'⟩
  · have h3 : rootW W6.T 1 ^ 3 = 1 := by decide +kernel
    have h : N6.r 1 * (rootW W6.T 1 * N6.r 1 * rootW W6.T 1 ^ 2) =
        rootW W6.T 1 ^ 2 * N6.r 1 * rootW W6.T 1 := by decide +kernel
    have h' : N6.r' 1 * (rootW W6.T 1 * N6.r' 1 * rootW W6.T 1 ^ 2) =
        rootW W6.T 1 ^ 2 * N6.r' 1 * rootW W6.T 1 := by decide +kernel
    exact ⟨rootRel_of_mul_pow (u := N6.r 1) h3 h,
      rootRel_of_mul_pow (u := N6.r' 1) h3 h'⟩

private theorem root_dist6_r0 (a a' : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r 0) =
        cjp (rootW W6.T 0) a' (N6.r 0) → a = a' := by
  simp only [cjp_c6R0]
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist6_rp0 (a a' : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r' 0) =
        cjp (rootW W6.T 0) a' (N6.r' 0) → a = a' := by
  simp only [cjp_c6R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist6_x0 (a a' : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r 0) ≠
      cjp (rootW W6.T 0) a' (N6.r' 0) := by
  simp only [cjp_c6R0, cjp_c6R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist6_r1 (a a' : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r 1) =
        cjp (rootW W6.T 1) a' (N6.r 1) → a = a' := by
  simp only [cjp_c6R1]
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist6_rp1 (a a' : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r' 1) =
        cjp (rootW W6.T 1) a' (N6.r' 1) → a = a' := by
  simp only [cjp_c6R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist6_x1 (a a' : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r 1) ≠
      cjp (rootW W6.T 1) a' (N6.r' 1) := by
  simp only [cjp_c6R1, cjp_c6R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

theorem root_dist_SL6 : ∀ j, ∀ a a' : Fin 3,
    (cjp (rootW W6.T j) a (N6.r j) = cjp (rootW W6.T j) a' (N6.r j) → a = a') ∧
    (cjp (rootW W6.T j) a (N6.r' j) = cjp (rootW W6.T j) a' (N6.r' j) → a = a') ∧
    cjp (rootW W6.T j) a (N6.r j) ≠ cjp (rootW W6.T j) a' (N6.r' j) := by
  intro j
  fin_cases j
  · intro a a'
    exact ⟨root_dist6_r0 a a', root_dist6_rp0 a a', root_dist6_x0 a a'⟩
  · intro a a'
    exact ⟨root_dist6_r1 a a', root_dist6_rp1 a a', root_dist6_x1 a a'⟩

theorem braid_SL6 : ∀ j, N6.r j * N6.r' j * N6.r j = N6.r' j * N6.r j * N6.r' j := by
  decide +kernel

private theorem braid_eq6_0 (a a' : Fin 3) :
    cjp (rootW W6.T 0) a (N6.r 0) *
        cjp (rootW W6.T 0) a' (N6.r' 0) *
        cjp (rootW W6.T 0) a (N6.r 0) =
      cjp (rootW W6.T 0) a' (N6.r' 0) *
        cjp (rootW W6.T 0) a (N6.r 0) *
        cjp (rootW W6.T 0) a' (N6.r' 0) → a = a' := by
  simp only [cjp_c6R0, cjp_c6R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem braid_eq6_1 (a a' : Fin 3) :
    cjp (rootW W6.T 1) a (N6.r 1) *
        cjp (rootW W6.T 1) a' (N6.r' 1) *
        cjp (rootW W6.T 1) a (N6.r 1) =
      cjp (rootW W6.T 1) a' (N6.r' 1) *
        cjp (rootW W6.T 1) a (N6.r 1) *
        cjp (rootW W6.T 1) a' (N6.r' 1) → a = a' := by
  simp only [cjp_c6R1, cjp_c6R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

theorem braid_eq_SL6 : ∀ j, ∀ a a' : Fin 3,
    cjp (rootW W6.T j) a (N6.r j) * cjp (rootW W6.T j) a' (N6.r' j) *
        cjp (rootW W6.T j) a (N6.r j) =
      cjp (rootW W6.T j) a' (N6.r' j) * cjp (rootW W6.T j) a (N6.r j) *
        cjp (rootW W6.T j) a' (N6.r' j) → a = a' := by
  intro j
  fin_cases j
  · intro a a'
    exact braid_eq6_0 a a'
  · intro a a'
    exact braid_eq6_1 a a'

theorem g_pow_SL6 : gOf N6.r N6.r' ^ 7 = 1 := by
  decide +kernel

theorem g_ne_SL6 : gOf N6.r N6.r' ≠ 1 := by
  decide +kernel

private def caT1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 1, 0, 0, 0]

private def caT2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private theorem caT1M_sq : caT1M * caT1M = 1 := by decide +kernel

private theorem caT2M_sq : caT2M * caT2M = 1 := by decide +kernel

private def caT1 : SL(6, ZMod 2) := W6.mkSL6 caT1M caT1M caT1M_sq

private def caT2 : SL(6, ZMod 2) := W6.mkSL6 caT2M caT2M caT2M_sq

private def caA : Matrix (Fin 6) (Fin 6) (ZMod 2) := caT1M * caT2M

private theorem caT1M_comm : caT1M * (W6.t2M * W6.t3M) = W6.t2M * W6.t3M * caT1M := by
  decide +kernel

private theorem caT2M_comm : caT2M * (W6.t2M * W6.t3M) = W6.t2M * W6.t3M * caT2M := by
  decide +kernel

private theorem caT1T2_eq : (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) + caA ^ 2 + caA ^ 3 =
    W6.t2M * W6.t3M := by
  decide +kernel

private theorem caT1_sq : caT1 * caT1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact caT1M_sq

private theorem caT2_sq : caT2 * caT2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact caT2M_sq

private theorem caT1_comm : caT1 * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * caT1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, W6.coe_T 1, W6.coe_T 2]
  exact caT1M_comm

private theorem caT2_comm : caT2 * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * caT2 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, W6.coe_T 1, W6.coe_T 2]
  exact caT2M_comm

private theorem ca_centralizer (y : SL(6, ZMod 2)) (hy1 : y * caT1 = caT1 * y)
    (hy2 : y * caT2 = caT2 * y) :
    y * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * y := by
  have hc1 : (caT1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = caT1M := rfl
  have hc2 : (caT2 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = caT2M := rfl
  have hy1m : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) * caT1M =
      caT1M * (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hy1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [hc1] using h
  have hy2m : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) * caT2M =
      caT2M * (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hy2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [hc2] using h
  have hYA : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) * caA =
      caA * (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [caA, ← mul_assoc, hy1m, mul_assoc, hy2m, ← mul_assoc]
  have h2 : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) * caA ^ 2 =
      caA ^ 2 * (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [pow_two, ← mul_assoc, hYA, mul_assoc, hYA, ← mul_assoc]
  have hA3 : caA ^ 3 = caA * caA ^ 2 := by simpa using pow_succ' caA 2
  have h3 : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) * caA ^ 3 =
      caA ^ 3 * (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [hA3, ← mul_assoc, hYA, mul_assoc, h2, ← mul_assoc]
  have hpoly : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ((1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) + caA ^ 2 + caA ^ 3) =
      ((1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) + caA ^ 2 + caA ^ 3) *
        (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    simp only [mul_add, add_mul, mul_one, one_mul]
    rw [h2, h3]
  rw [caT1T2_eq] at hpoly
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    W6.coe_T 1, W6.coe_T 2]
  exact hpoly

theorem caseA_SL6 : ∃ t₁ t₂ : SL(6, ZMod 2), t₁ * t₁ = 1 ∧ t₂ * t₂ = 1 ∧
    t₁ * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * t₁ ∧
    t₂ * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * t₂ ∧
    ∀ y : SL(6, ZMod 2), y * t₁ = t₁ * y → y * t₂ = t₂ * y →
      y * (W6.T 1 * W6.T 2) = W6.T 1 * W6.T 2 * y := by
  exact ⟨caT1, caT2, caT1_sq, caT2_sq, caT1_comm, caT2_comm, ca_centralizer⟩

private def c7R0M : Fin 3 → Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  ![!![1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 1, 0, 0, 0;
      0, 1, 1, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 1, 1, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1]]

private theorem c7R0M_sq (a : Fin 3) : c7R0M a * c7R0M a = 1 := by
  fin_cases a <;> decide +kernel

private def c7R0 (a : Fin 3) : SL(7, ZMod 2) :=
  W7.mkSL7 (c7R0M a) (c7R0M a) (c7R0M_sq a)

private theorem cjp_c7R0 (a : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r 0) = c7R0 a := by
  change cjp (W7.T 0) a (N7.r 0) = c7R0 a
  rw [cjp_eq_mul_pow_sub (W7.pow_T 0)]
  fin_cases a <;> decide +kernel

private def c7R0'M : Fin 3 → Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 0, 0;
      0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      1, 1, 1, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0;
      1, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1]]

private theorem c7R0'M_sq (a : Fin 3) : c7R0'M a * c7R0'M a = 1 := by
  fin_cases a <;> decide +kernel

private def c7R0' (a : Fin 3) : SL(7, ZMod 2) :=
  W7.mkSL7 (c7R0'M a) (c7R0'M a) (c7R0'M_sq a)

private theorem cjp_c7R0' (a : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r' 0) = c7R0' a := by
  change cjp (W7.T 0) a (N7.r' 0) = c7R0' a
  rw [cjp_eq_mul_pow_sub (W7.pow_T 0)]
  fin_cases a <;> decide +kernel

private def c7R1M : Fin 3 → Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 1, 1, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 1, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1]]

private theorem c7R1M_sq (a : Fin 3) : c7R1M a * c7R1M a = 1 := by
  fin_cases a <;> decide +kernel

private def c7R1 (a : Fin 3) : SL(7, ZMod 2) :=
  W7.mkSL7 (c7R1M a) (c7R1M a) (c7R1M_sq a)

private theorem cjp_c7R1 (a : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r 1) = c7R1 a := by
  change cjp (W7.T 1) a (N7.r 1) = c7R1 a
  rw [cjp_eq_mul_pow_sub (W7.pow_T 1)]
  fin_cases a <;> decide +kernel

private def c7R1'M : Fin 3 → Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 1, 1, 0, 0;
      0, 0, 1, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1],
   !![1, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 1]]

private theorem c7R1'M_sq (a : Fin 3) : c7R1'M a * c7R1'M a = 1 := by
  fin_cases a <;> decide +kernel

private def c7R1' (a : Fin 3) : SL(7, ZMod 2) :=
  W7.mkSL7 (c7R1'M a) (c7R1'M a) (c7R1'M_sq a)

private theorem cjp_c7R1' (a : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r' 1) = c7R1' a := by
  change cjp (W7.T 1) a (N7.r' 1) = c7R1' a
  rw [cjp_eq_mul_pow_sub (W7.pow_T 1)]
  fin_cases a <;> decide +kernel


theorem pi_z_SL7 : ∀ i, W7.tw * W7.T i * W7.tw⁻¹ = W7.T (finRotate 3 i) := by
  intro i
  fin_cases i
  · simpa using W7.conj0_T
  · simpa using W7.conj1_T
  · simpa using W7.conj2_T

theorem x0_z0_SL7 : N7.x0 * W7.T 0 * N7.x0⁻¹ = W7.T 0 := by
  have h : N7.x0 * W7.T 0 = W7.T 0 * N7.x0 := by decide +kernel
  rw [h]
  group

theorem x0_z1_SL7 : N7.x0 * W7.T 1 * N7.x0⁻¹ = W7.T 2 := by
  have h : N7.x0 * W7.T 1 = W7.T 2 * N7.x0 := by decide +kernel
  rw [h]
  group

theorem x0_z2_SL7 : N7.x0 * W7.T 2 * N7.x0⁻¹ = W7.T 1 := by
  have h : N7.x0 * W7.T 2 = W7.T 1 * N7.x0 := by decide +kernel
  rw [h]
  group

theorem root_sq_SL7 : ∀ j, N7.r j * N7.r j = 1 ∧ N7.r' j * N7.r' j = 1 := by
  decide +kernel

theorem root_comm_SL7 : ∀ j, N7.r j * rootK₁ W7.T j = rootK₁ W7.T j * N7.r j ∧
    N7.r j * rootK₂ W7.T j = rootK₂ W7.T j * N7.r j ∧
    N7.r' j * rootK₁ W7.T j = rootK₁ W7.T j * N7.r' j ∧
    N7.r' j * rootK₂ W7.T j = rootK₂ W7.T j * N7.r' j := by
  decide +kernel

theorem root_rel_SL7 : ∀ j, RootRel (rootW W7.T j) (N7.r j) ∧ RootRel (rootW W7.T j) (N7.r' j) := by
  intro j
  fin_cases j
  · have h3 : rootW W7.T 0 ^ 3 = 1 := by decide +kernel
    have h : N7.r 0 * (rootW W7.T 0 * N7.r 0 * rootW W7.T 0 ^ 2) =
        rootW W7.T 0 ^ 2 * N7.r 0 * rootW W7.T 0 := by decide +kernel
    have h' : N7.r' 0 * (rootW W7.T 0 * N7.r' 0 * rootW W7.T 0 ^ 2) =
        rootW W7.T 0 ^ 2 * N7.r' 0 * rootW W7.T 0 := by decide +kernel
    exact ⟨rootRel_of_mul_pow (u := N7.r 0) h3 h,
      rootRel_of_mul_pow (u := N7.r' 0) h3 h'⟩
  · have h3 : rootW W7.T 1 ^ 3 = 1 := by decide +kernel
    have h : N7.r 1 * (rootW W7.T 1 * N7.r 1 * rootW W7.T 1 ^ 2) =
        rootW W7.T 1 ^ 2 * N7.r 1 * rootW W7.T 1 := by decide +kernel
    have h' : N7.r' 1 * (rootW W7.T 1 * N7.r' 1 * rootW W7.T 1 ^ 2) =
        rootW W7.T 1 ^ 2 * N7.r' 1 * rootW W7.T 1 := by decide +kernel
    exact ⟨rootRel_of_mul_pow (u := N7.r 1) h3 h,
      rootRel_of_mul_pow (u := N7.r' 1) h3 h'⟩

private theorem root_dist7_r0 (a a' : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r 0) =
        cjp (rootW W7.T 0) a' (N7.r 0) → a = a' := by
  simp only [cjp_c7R0]
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist7_rp0 (a a' : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r' 0) =
        cjp (rootW W7.T 0) a' (N7.r' 0) → a = a' := by
  simp only [cjp_c7R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist7_x0 (a a' : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r 0) ≠
      cjp (rootW W7.T 0) a' (N7.r' 0) := by
  simp only [cjp_c7R0, cjp_c7R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist7_r1 (a a' : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r 1) =
        cjp (rootW W7.T 1) a' (N7.r 1) → a = a' := by
  simp only [cjp_c7R1]
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist7_rp1 (a a' : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r' 1) =
        cjp (rootW W7.T 1) a' (N7.r' 1) → a = a' := by
  simp only [cjp_c7R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem root_dist7_x1 (a a' : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r 1) ≠
      cjp (rootW W7.T 1) a' (N7.r' 1) := by
  simp only [cjp_c7R1, cjp_c7R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

theorem root_dist_SL7 : ∀ j, ∀ a a' : Fin 3,
    (cjp (rootW W7.T j) a (N7.r j) = cjp (rootW W7.T j) a' (N7.r j) → a = a') ∧
    (cjp (rootW W7.T j) a (N7.r' j) = cjp (rootW W7.T j) a' (N7.r' j) → a = a') ∧
    cjp (rootW W7.T j) a (N7.r j) ≠ cjp (rootW W7.T j) a' (N7.r' j) := by
  intro j
  fin_cases j
  · intro a a'
    exact ⟨root_dist7_r0 a a', root_dist7_rp0 a a', root_dist7_x0 a a'⟩
  · intro a a'
    exact ⟨root_dist7_r1 a a', root_dist7_rp1 a a', root_dist7_x1 a a'⟩

theorem braid_SL7 : ∀ j, N7.r j * N7.r' j * N7.r j = N7.r' j * N7.r j * N7.r' j := by
  decide +kernel

private theorem braid_eq7_0 (a a' : Fin 3) :
    cjp (rootW W7.T 0) a (N7.r 0) *
        cjp (rootW W7.T 0) a' (N7.r' 0) *
        cjp (rootW W7.T 0) a (N7.r 0) =
      cjp (rootW W7.T 0) a' (N7.r' 0) *
        cjp (rootW W7.T 0) a (N7.r 0) *
        cjp (rootW W7.T 0) a' (N7.r' 0) → a = a' := by
  simp only [cjp_c7R0, cjp_c7R0']
  fin_cases a <;> fin_cases a' <;> decide +kernel

private theorem braid_eq7_1 (a a' : Fin 3) :
    cjp (rootW W7.T 1) a (N7.r 1) *
        cjp (rootW W7.T 1) a' (N7.r' 1) *
        cjp (rootW W7.T 1) a (N7.r 1) =
      cjp (rootW W7.T 1) a' (N7.r' 1) *
        cjp (rootW W7.T 1) a (N7.r 1) *
        cjp (rootW W7.T 1) a' (N7.r' 1) → a = a' := by
  simp only [cjp_c7R1, cjp_c7R1']
  fin_cases a <;> fin_cases a' <;> decide +kernel

theorem braid_eq_SL7 : ∀ j, ∀ a a' : Fin 3,
    cjp (rootW W7.T j) a (N7.r j) * cjp (rootW W7.T j) a' (N7.r' j) *
        cjp (rootW W7.T j) a (N7.r j) =
      cjp (rootW W7.T j) a' (N7.r' j) * cjp (rootW W7.T j) a (N7.r j) *
        cjp (rootW W7.T j) a' (N7.r' j) → a = a' := by
  intro j
  fin_cases j
  · intro a a'
    exact braid_eq7_0 a a'
  · intro a a'
    exact braid_eq7_1 a a'

theorem g_pow_SL7 : gOf N7.r N7.r' ^ 7 = 1 := by
  decide +kernel

theorem g_ne_SL7 : gOf N7.r N7.r' ≠ 1 := by
  decide +kernel

private def caT1M7 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1]

private def caT2M7 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 1, 0;
     0, 0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

private theorem caT1M7_sq : caT1M7 * caT1M7 = 1 := by decide +kernel

private theorem caT2M7_sq : caT2M7 * caT2M7 = 1 := by decide +kernel

private def caT1_7 : SL(7, ZMod 2) := W7.mkSL7 caT1M7 caT1M7 caT1M7_sq

private def caT2_7 : SL(7, ZMod 2) := W7.mkSL7 caT2M7 caT2M7 caT2M7_sq

private def caA7 : Matrix (Fin 7) (Fin 7) (ZMod 2) := caT1M7 * caT2M7

private theorem caT1M7_comm : caT1M7 * (W7.t2M * W7.t3M) = W7.t2M * W7.t3M * caT1M7 := by
  decide +kernel

private theorem caT2M7_comm : caT2M7 * (W7.t2M * W7.t3M) = W7.t2M * W7.t3M * caT2M7 := by
  decide +kernel

private theorem caT1T2_eq7 : (1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + caA7 ^ 2 + caA7 ^ 3 =
    W7.t2M * W7.t3M := by
  decide +kernel

private theorem caT1_7_sq : caT1_7 * caT1_7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact caT1M7_sq

private theorem caT2_7_sq : caT2_7 * caT2_7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact caT2M7_sq

private theorem caT1_7_comm : caT1_7 * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * caT1_7 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, W7.coe_T 1, W7.coe_T 2]
  exact caT1M7_comm

private theorem caT2_7_comm : caT2_7 * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * caT2_7 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, W7.coe_T 1, W7.coe_T 2]
  exact caT2M7_comm

private theorem ca_centralizer7 (y : SL(7, ZMod 2)) (hy1 : y * caT1_7 = caT1_7 * y)
    (hy2 : y * caT2_7 = caT2_7 * y) :
    y * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * y := by
  have hc1 : (caT1_7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) = caT1M7 := rfl
  have hc2 : (caT2_7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) = caT2M7 := rfl
  have hy1m : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) * caT1M7 =
      caT1M7 * (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hy1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [hc1] using h
  have hy2m : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) * caT2M7 =
      caT2M7 * (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hy2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [hc2] using h
  have hYA : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) * caA7 =
      caA7 * (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [caA7, ← mul_assoc, hy1m, mul_assoc, hy2m, ← mul_assoc]
  have h2 : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) * caA7 ^ 2 =
      caA7 ^ 2 * (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [pow_two, ← mul_assoc, hYA, mul_assoc, hYA, ← mul_assoc]
  have hA3 : caA7 ^ 3 = caA7 * caA7 ^ 2 := by simpa using pow_succ' caA7 2
  have h3 : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) * caA7 ^ 3 =
      caA7 ^ 3 * (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [hA3, ← mul_assoc, hYA, mul_assoc, h2, ← mul_assoc]
  have hpoly : (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + caA7 ^ 2 + caA7 ^ 3) =
      ((1 : Matrix (Fin 7) (Fin 7) (ZMod 2)) + caA7 ^ 2 + caA7 ^ 3) *
        (y : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    simp only [mul_add, add_mul, mul_one, one_mul]
    rw [h2, h3]
  rw [caT1T2_eq7] at hpoly
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    W7.coe_T 1, W7.coe_T 2]
  exact hpoly

theorem caseA_SL7 : ∃ t₁ t₂ : SL(7, ZMod 2), t₁ * t₁ = 1 ∧ t₂ * t₂ = 1 ∧
    t₁ * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * t₁ ∧
    t₂ * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * t₂ ∧
    ∀ y : SL(7, ZMod 2), y * t₁ = t₁ * y → y * t₂ = t₂ * y →
      y * (W7.T 1 * W7.T 2) = W7.T 1 * W7.T 2 * y := by
  exact ⟨caT1_7, caT2_7, caT1_7_sq, caT2_7_sq, caT1_7_comm, caT2_7_comm, ca_centralizer7⟩

end CFSG.StandardType.GGFF

end
