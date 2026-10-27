module

public import CFSG.RankThree.Classical2.SLnSemilinearRigidity

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix

@[expose] def HeisPair (G : Type*) [Group G] : Prop :=
  ∃ y p u : G, u ≠ 1 ∧ u ^ 3 = 1 ∧ (∀ g : G, g * u = u * g) ∧ p * y * p⁻¹ * y⁻¹ = u

theorem HeisPair.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : HeisPair G) :
    HeisPair H := by
  obtain ⟨y, p, u, hu1, hu3, huc, hup⟩ := h
  refine ⟨e y, e p, e u, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hu1 (e.injective (by rw [h1, map_one]))
  · rw [← map_pow, hu3, map_one]
  · intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, huc g']
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hup]

section SL3

variable {F : Type*} [Field F]

theorem sq_ne_one_of_cube {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  apply hω1
  have h1 : ω = ω ^ 3 * (ω ^ 2)⁻¹ := by
    have : ω ^ 2 ≠ 0 := by
      intro h0
      rw [h0] at h
      exact zero_ne_one h
    field_simp
  rw [h1, hω3, h]
  simp

theorem det_diag_heis {ω : F} (hω3 : ω ^ 3 = 1) :
    (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [one_mul, ← pow_succ']
  exact hω3


theorem heisPair_SL3 {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    HeisPair (Matrix.SpecialLinearGroup (Fin 3) F) := by
  classical
  have hdetP : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Matrix.det_fin_three]
    simp
  have hdetU : (Matrix.scalar (Fin 3) (ω ^ 2)).det = 1 := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  let Y : Matrix.SpecialLinearGroup (Fin 3) F := ⟨Matrix.diagonal ![1, ω, ω ^ 2], det_diag_heis hω3⟩
  let P : Matrix.SpecialLinearGroup (Fin 3) F := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], hdetP⟩
  let U : Matrix.SpecialLinearGroup (Fin 3) F := ⟨Matrix.scalar (Fin 3) (ω ^ 2), hdetU⟩
  have hω4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [hω3, one_mul]
  have key : P * Y = U * (Y * P) := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y, P, U, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.scalar_apply,
        Matrix.diagonal_mul] <;>
      first | rfl | (linear_combination (-1 : F) * hω3) | (linear_combination (-ω) * hω3)
  refine ⟨Y, P, U, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F) 0 0) h1
    simp only [U, Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h2
    exact sq_ne_one_of_cube hω3 hω1 h2
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change (Matrix.scalar (Fin 3) (ω ^ 2)) ^ 3 = 1
    rw [← map_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow, map_one]
  · intro g
    have hU : U ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨ω ^ 2, ?_, rfl⟩
      rw [Fintype.card_fin, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
    exact Subgroup.mem_center_iff.mp hU g
  · calc P * Y * P⁻¹ * Y⁻¹ = U * (Y * P) * P⁻¹ * Y⁻¹ := by rw [key]
      _ = U := by group

end SL3

section Unitary

open CFSG.RankThree.Classical2

variable {Ω : Type*} [Field Ω]

theorem isUnit_det_permMatrix_finRotate :
    IsUnit ((finRotate 3).permMatrix Ω).det := by
  rw [Matrix.det_permutation]
  have : Equiv.Perm.sign (finRotate 3) = 1 := by
    have := sign_finRotate 2
    simpa using this
  rw [this]
  simp

theorem heisPair_unitary {q : ℕ} (hq : 1 ≤ q) {ω : Ω} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωq : ω ^ (q + 1) = 1) (U : Subgroup (GL (Fin 3) Ω))
    (hU : (U : Set (GL (Fin 3) Ω)) = unitarySet q 3) : HeisPair U := by
  classical
  have hdetY : IsUnit (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) Ω).det := by
    rw [det_diag_heis hω3]
    exact isUnit_one
  have hYU : (Matrix.nonsingInvUnit (Matrix.diagonal ![1, ω, ω ^ 2]) hdetY : GL (Fin 3) Ω) ∈ U := by
    have : (Matrix.nonsingInvUnit (Matrix.diagonal ![1, ω, ω ^ 2]) hdetY : GL (Fin 3) Ω) ∈
        (U : Set (GL (Fin 3) Ω)) := by
      rw [hU]
      refine diagonal_mem_unitary hq ?_ ?_ hdetY
      · intro i
        fin_cases i
        · simp
        · simpa using hωq
        · simp only [Fin.reduceFinMk, Matrix.cons_val]
          rw [← pow_mul, mul_comm, pow_mul, hωq, one_pow]
      · rw [Fin.prod_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
        rw [one_mul, ← pow_succ']
        exact hω3
    exact this
  have hsgn : Equiv.Perm.sign (finRotate 3) = 1 := by
    have := sign_finRotate 2
    simpa using this
  have hPU : (Matrix.nonsingInvUnit ((finRotate 3).permMatrix Ω) isUnit_det_permMatrix_finRotate :
      GL (Fin 3) Ω) ∈ U := by
    have : (Matrix.nonsingInvUnit ((finRotate 3).permMatrix Ω) isUnit_det_permMatrix_finRotate :
        GL (Fin 3) Ω) ∈ (U : Set (GL (Fin 3) Ω)) := by
      rw [hU]
      exact permMatrix_mem_unitary hq hsgn isUnit_det_permMatrix_finRotate
    exact this
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hω3
    exact zero_ne_one hω3
  set Yg : GL (Fin 3) Ω :=
    Matrix.nonsingInvUnit (Matrix.diagonal ![1, ω, ω ^ 2]) hdetY with hYg
  set Pg : GL (Fin 3) Ω :=
    Matrix.nonsingInvUnit ((finRotate 3).permMatrix Ω) isUnit_det_permMatrix_finRotate with hPg
  set Sg : GL (Fin 3) Ω := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) with hSg
  have hSgm : (Sg : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) ω := by
    rw [hSg, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have key : Pg * Yg = Sg * (Yg * Pg) := by
    apply Units.ext
    simp only [Units.val_mul, hSgm]
    change (finRotate 3).permMatrix Ω * Matrix.diagonal ![1, ω, ω ^ 2] =
      Matrix.scalar (Fin 3) ω * (Matrix.diagonal ![1, ω, ω ^ 2] * (finRotate 3).permMatrix Ω)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, finRotate_succ_apply, Matrix.scalar_apply,
        Matrix.diagonal_mul] <;>
      first | ring1 | (linear_combination (-1 : Ω) * hω3)
  have hcomm : Pg * Yg * Pg⁻¹ * Yg⁻¹ = Sg := by
    calc Pg * Yg * Pg⁻¹ * Yg⁻¹ = Sg * (Yg * Pg) * Pg⁻¹ * Yg⁻¹ := by rw [key]
      _ = Sg := by group
  let yu : U := ⟨Yg, hYU⟩
  let pu : U := ⟨Pg, hPU⟩
  have hcomm' : ((pu * yu * pu⁻¹ * yu⁻¹ : U) : GL (Fin 3) Ω) = Sg := by
    simpa using hcomm
  refine ⟨yu, pu, pu * yu * pu⁻¹ * yu⁻¹, ?_, ?_, ?_, rfl⟩
  · intro h1
    have h2 := congrArg (fun g : U => ((g : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) 0 0) h1
    simp only [hcomm', hSgm, Matrix.scalar_apply, Matrix.diagonal_apply_eq, OneMemClass.coe_one,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact hω1 h2
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hcomm', OneMemClass.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hSgm, Units.val_one]
    rw [← map_pow, hω3, map_one]
  · intro g
    apply Subtype.ext
    change (g : GL (Fin 3) Ω) * ((pu * yu * pu⁻¹ * yu⁻¹ : U) : GL (Fin 3) Ω) =
      ((pu * yu * pu⁻¹ * yu⁻¹ : U) : GL (Fin 3) Ω) * (g : GL (Fin 3) Ω)
    rw [hcomm']
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hSgm]
    exact (Matrix.scalar_commute ω (Commute.all ω) _).symm

end Unitary

section InSubgroup

variable {G : Type*} [Group G]

@[expose] def HeisIn (D : Subgroup G) : Prop :=
  ∃ y ∈ D, ∃ p ∈ D, ∃ u ∈ D, u ≠ 1 ∧ u ^ 3 = 1 ∧ (∀ d ∈ D, u * d = d * u) ∧ p * y * p⁻¹ * y⁻¹ = u

@[expose] def CubeCenter (D : Subgroup G) : Prop :=
  ∀ t ∈ D, (∀ d ∈ D, t * d = d * t) → t ^ 3 = 1

theorem heisIn_of_mulEquiv {H : Type*} [Group H] (D : Subgroup G) (e : D ≃* H) (h : HeisPair H) :
    HeisIn D := by
  obtain ⟨y, p, u, hu1, hu3, huc, hup⟩ := (HeisPair.of_mulEquiv e.symm h : HeisPair D)
  refine ⟨y, y.2, p, p.2, u, u.2, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hu1 (Subtype.ext h1)
  · exact congrArg Subtype.val hu3
  · intro d hd
    exact (congrArg Subtype.val (huc ⟨d, hd⟩)).symm
  · exact congrArg Subtype.val hup

theorem layerSub_le_self (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

end InSubgroup

end CFSG.RankThree.PartTwo.Sec4.E27
