module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open Matrix

variable {K : Type} [Field K]

@[expose] def rankOne (u ψ : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => u i * ψ j

@[expose] def elemMat (u ψ : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  1 + rankOne u ψ

theorem det_elemMat (u ψ : Fin 3 → K) :
    (elemMat u ψ).det = 1 + ψ ⬝ᵥ u := by
  simp only [elemMat, rankOne, Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]
  simp [Matrix.one_apply]
  ring

theorem rankOne_mul_rankOne (u ψ φ : Fin 3 → K) :
    rankOne u ψ * rankOne u φ = (ψ ⬝ᵥ u) • rankOne u φ := by
  ext i j
  simp [rankOne, Matrix.mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

theorem rankOne_add (u ψ φ : Fin 3 → K) :
    rankOne u ψ + rankOne u φ = rankOne u (ψ + φ) := by
  ext i j
  simp [rankOne, mul_add]

theorem elemMat_zero (u : Fin 3 → K) : elemMat u 0 = 1 := by
  ext i j
  simp [elemMat, rankOne]

theorem elemMat_mul (u ψ φ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) :
    elemMat u ψ * elemMat u φ = elemMat u (ψ + φ) := by
  simp only [elemMat, add_mul, mul_add, one_mul, mul_one, rankOne_mul_rankOne, hψ, zero_smul,
    add_zero]
  rw [← rankOne_add]
  abel

theorem elemMat_neg_mul (u ψ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) :
    elemMat u (-ψ) * elemMat u ψ = 1 := by
  rw [elemMat_mul u (-ψ) ψ (by rw [neg_dotProduct, hψ, neg_zero]), neg_add_cancel, elemMat_zero]

theorem elemMat_mul_neg (u ψ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) :
    elemMat u ψ * elemMat u (-ψ) = 1 := by
  rw [elemMat_mul u ψ (-ψ) hψ, add_neg_cancel, elemMat_zero]

@[expose] def elemUnit (u ψ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) : GL (Fin 3) K :=
  ⟨elemMat u ψ, elemMat u (-ψ), elemMat_mul_neg u ψ hψ, elemMat_neg_mul u ψ hψ⟩

theorem coe_elemUnit (u ψ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) :
    ((elemUnit u ψ hψ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = elemMat u ψ :=
  rfl

theorem perp_conj {A B : Matrix (Fin 3) (Fin 3) K} (hBA : B * A = 1) {u ψ : Fin 3 → K} {l : K}
    (hAu : A *ᵥ u = l • u) (hψ : ψ ⬝ᵥ u = 0) :
    (l • (ψ ᵥ* B)) ⬝ᵥ u = 0 := by
  have h1 : l • (B *ᵥ u) = u := by
    have h := congrArg (B *ᵥ ·) hAu
    simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    exact h.symm
  rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, ← dotProduct_smul, h1, hψ]

theorem conj_elemMat {A B : Matrix (Fin 3) (Fin 3) K} (hAB : A * B = 1) {u ψ : Fin 3 → K}
    {l : K} (hAu : A *ᵥ u = l • u) :
    A * elemMat u ψ * B = elemMat u (l • (ψ ᵥ* B)) := by
  have key : A * elemMat u ψ * B = A * B + A * rankOne u ψ * B := by
    simp only [elemMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
  rw [key, hAB]
  ext i j
  have hi : A i 0 * u 0 + A i 1 * u 1 + A i 2 * u 2 = l * u i := by
    have h := congrFun hAu i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] at h
    exact h
  simp only [elemMat, rankOne, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  linear_combination (ψ 0 * B 0 j + ψ 1 * B 1 j + ψ 2 * B 2 j) * hi

@[expose] def rootSet (u : Fin 3 → K) : Set (GL (Fin 3) K) :=
  {g | ∃ ψ : Fin 3 → K, ψ ⬝ᵥ u = 0 ∧ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = elemMat u ψ}

@[expose] def rootGL (u : Fin 3 → K) : Subgroup (GL (Fin 3) K) where
  carrier := rootSet u
  mul_mem' := by
    rintro a b ⟨ψ, hψ, ha⟩ ⟨φ, hφ, hb⟩
    refine ⟨ψ + φ, by rw [add_dotProduct, hψ, hφ, add_zero], ?_⟩
    rw [Units.val_mul, ha, hb, elemMat_mul u ψ φ hψ]
  one_mem' := ⟨0, zero_dotProduct _, by rw [Units.val_one, elemMat_zero]⟩
  inv_mem' := by
    rintro g ⟨ψ, hψ, hg⟩
    refine ⟨-ψ, by rw [neg_dotProduct, hψ, neg_zero], ?_⟩
    rw [Matrix.coe_units_inv, hg]
    exact Matrix.inv_eq_right_inv (elemMat_mul_neg u ψ hψ)

theorem mem_rootGL {u : Fin 3 → K} {g : GL (Fin 3) K} :
    g ∈ rootGL u ↔ ∃ ψ : Fin 3 → K, ψ ⬝ᵥ u = 0 ∧
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = elemMat u ψ :=
  Iff.rfl

theorem elemUnit_mem_stated (u ψ : Fin 3 → K) (hψ : ψ ⬝ᵥ u = 0) :
    elemUnit u ψ hψ ∈ CFSG.Open.StatedSL 3 K := by
  apply Subgroup.subset_closure
  show ((elemUnit u ψ hψ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
  rw [coe_elemUnit, det_elemMat, hψ, add_zero]

theorem exists_perp_ne_zero {u : Fin 3 → K} (hu : u ≠ 0) :
    ∃ ψ : Fin 3 → K, ψ ⬝ᵥ u = 0 ∧ ψ ≠ 0 := by
  by_cases h01 : u 0 = 0 ∧ u 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three, h01.1]
    · intro h
      have := congrFun h 0
      simp at this
  · refine ⟨![u 1, -u 0, 0], ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_three] <;> ring
    · intro h
      have h0 : u 1 = 0 := by simpa using congrFun h 0
      have h1 : u 0 = 0 := by simpa using congrFun h 1
      exact h01 ⟨h1, h0⟩

theorem elemMat_ne_one {u ψ : Fin 3 → K} (hu : u ≠ 0) (hψ0 : ψ ≠ 0) :
    elemMat u ψ ≠ 1 := by
  intro h
  have hR : rankOne u ψ = 0 := by
    simpa [elemMat] using h
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu (funext hc)
  obtain ⟨j, hj⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hψ0 (funext hc)
  have := congrFun (congrFun hR i) j
  simp [rankOne, hi, hj] at this

@[expose] def rootSL (u : Fin 3 → K) : Subgroup (CFSG.Open.StatedSL 3 K) :=
  (rootGL u).subgroupOf (CFSG.Open.StatedSL 3 K)

theorem mem_rootSL {u : Fin 3 → K} (x : CFSG.Open.StatedSL 3 K) :
    x ∈ rootSL u ↔ (x : GL (Fin 3) K) ∈ rootGL u :=
  Subgroup.mem_subgroupOf

theorem rootSL_ne_bot {u : Fin 3 → K} (hu : u ≠ 0) : rootSL u ≠ ⊥ := by
  obtain ⟨ψ, hψ, hψ0⟩ := exists_perp_ne_zero hu
  intro hbot
  have hx : (⟨elemUnit u ψ hψ, elemUnit_mem_stated u ψ hψ⟩ :
      CFSG.Open.StatedSL 3 K) ∈ rootSL u :=
    (mem_rootSL _).mpr ((mem_rootGL).mpr ⟨ψ, hψ, rfl⟩)
  rw [hbot, Subgroup.mem_bot] at hx
  have h1 : elemUnit u ψ hψ = 1 := congrArg Subtype.val hx
  have h2 : elemMat u ψ = 1 := by
    rw [← coe_elemUnit u ψ hψ, h1, Units.val_one]
  exact elemMat_ne_one hu hψ0 h2

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
