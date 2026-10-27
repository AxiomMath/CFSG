module

public import CFSG.RankThree.PartOne.SEITZU49.Frame

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Circ

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)
open CFSG.RankThree.PartOne.CTP.U5Eigen (shiftMat shiftMat_apply)

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem shiftMat_mulVec' (w : Fin 5 → K) : shiftMat *ᵥ w = fun s => w (s - 1) := by
  ext s
  simp [Matrix.mulVec, dotProduct, shiftMat_apply]

theorem shiftZ_mulVec (z : K) (v : Fin 5 → K) :
    shiftZ z *ᵥ v = ![z * v 4, v 0, v 1, v 2, v 3] := by
  ext i
  rw [shiftZ, ← Matrix.mulVec_mulVec, shiftMat_mulVec']
  fin_cases i
  · simp [Matrix.mulVec_diagonal]
    left
    rfl
  all_goals simp [Matrix.mulVec_diagonal]

theorem conjTr_shiftMat_mulVec' (w : Fin 5 → K) :
    conjTr σ shiftMat *ᵥ w = fun s => w (s + 1) := by
  ext s
  simp [conjTr, Matrix.mulVec, dotProduct, shiftMat_apply]
  rw [Finset.sum_eq_single (s + 1)]
  · simp
  · intro x _ hx
    have : ¬ s = x - 1 := fun h => hx ((eq_sub_iff_add_eq.mp h).symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem conjTr_diagonal' (t : Fin 5 → K) :
    conjTr σ (Matrix.diagonal t) = Matrix.diagonal (fun i => σ (t i)) := by
  ext i j
  simp [conjTr, Matrix.diagonal_apply, eq_comm]
  by_cases h : i = j
  · subst h; rfl
  · simp [h]

theorem conjTr_shiftZ_mulVec (z : K) (v : Fin 5 → K) :
    conjTr σ (shiftZ z) *ᵥ v = ![v 1, v 2, v 3, v 4, σ z * v 0] := by
  rw [shiftZ, conjTr_mul, ← Matrix.mulVec_mulVec, conjTr_shiftMat_mulVec', conjTr_diagonal']
  ext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

theorem eq_of_mulVec_eq {M N : Matrix (Fin 5) (Fin 5) K} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N :=
  Matrix.ext_of_mulVec_single fun _ => h _

theorem conjTr_shiftZ_mul (z : K) (hz : σ z * z = 1) :
    conjTr σ (shiftZ z) * shiftZ z = 1 := by
  apply eq_of_mulVec_eq
  intro v
  rw [← Matrix.mulVec_mulVec, shiftZ_mulVec, conjTr_shiftZ_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> simp
  rw [← mul_assoc, hz, one_mul]

theorem shiftZ_mul_conjTr (z : K) (hz : σ z * z = 1) :
    shiftZ z * conjTr σ (shiftZ z) = 1 :=
  mul_eq_one_comm.mp (conjTr_shiftZ_mul σ z hz)

theorem shiftZ_pow_five (z : K) : shiftZ z ^ 5 = z • (1 : Matrix (Fin 5) (Fin 5) K) := by
  apply eq_of_mulVec_eq
  intro v
  have e : shiftZ z ^ 5 = shiftZ z * (shiftZ z * (shiftZ z * (shiftZ z * shiftZ z))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, shiftZ_mulVec, shiftZ_mulVec, shiftZ_mulVec, shiftZ_mulVec,
    shiftZ_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> simp

theorem conjTr_smul' (c : K) (M : Matrix (Fin 5) (Fin 5) K) :
    conjTr σ (c • M) = σ c • conjTr σ M := by
  ext i j
  simp [conjTr]

theorem conjTr_pow' (M : Matrix (Fin 5) (Fin 5) K) (k : ℕ) :
    conjTr σ (M ^ k) = conjTr σ M ^ k := by
  induction k with
  | zero => simp [conjTr_one]
  | succ k ih => rw [pow_succ, conjTr_mul, ih, pow_succ']

theorem conjTr_conjTr' (hσ : ∀ c, σ (σ c) = c) (M : Matrix (Fin 5) (Fin 5) K) :
    conjTr σ (conjTr σ M) = M := by
  ext i j
  simp [conjTr, hσ]


theorem geom_left (h2 : (2 : K) = 0) (X : Matrix (Fin 5) (Fin 5) K) :
    (1 + X) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) = 1 + X ^ 5 := by
  have e : (1 + X) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) =
      1 + X ^ 5 + (2 : K) • (X + X ^ 2 + X ^ 3 + X ^ 4) := by
    rw [two_smul]; noncomm_ring
  rw [e, h2, zero_smul, add_zero]

theorem geom_right (h2 : (2 : K) = 0) (X : Matrix (Fin 5) (Fin 5) K) :
    (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X) = 1 + X ^ 5 := by
  have e : (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X) =
      1 + X ^ 5 + (2 : K) • (X + X ^ 2 + X ^ 3 + X ^ 4) := by
    rw [two_smul]; noncomm_ring
  rw [e, h2, zero_smul, add_zero]

variable {σ}

theorem exists_h1 (h2 : (2 : K) = 0) (hσ : ∀ c, σ (σ c) = c) {z ω : K} (hz : σ z * z = 1)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) (hD : 1 + ω ^ 2 * σ z ≠ 0) :
    ∃ (h1 : Matrix (Fin 5) (Fin 5) K) (c0 κ' : K), conjTr σ h1 * h1 = 1 ∧
      h1 * shiftZ z = shiftZ z * h1 ∧
      h1 *ᵥ ![1, 0, 0, 1, 0] = κ' • ![0, ω, ω, 1, 1] ∧ (h1 *ᵥ ![1, 0, 0, 0, 0]) 0 = c0 ∧
      c0 ≠ 0 ∧ κ' ≠ 0 := by
  classical
  have hGGs : shiftZ z * conjTr σ (shiftZ z) = 1 := shiftZ_mul_conjTr σ z hz
  have hGsG : conjTr σ (shiftZ z) * shiftZ z = 1 := conjTr_shiftZ_mul σ z hz
  have hcomm : Commute (shiftZ z) (conjTr σ (shiftZ z)) := hGGs.trans hGsG.symm
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  set G := shiftZ z with hG
  set Gs := conjTr σ G with hGs
  set X : Matrix (Fin 5) (Fin 5) K := ω • Gs with hX
  set A : Matrix (Fin 5) (Fin 5) K := 1 + ω • G with hA
  set A' : Matrix (Fin 5) (Fin 5) K := 1 + X with hA'
  set Xi : Matrix (Fin 5) (Fin 5) K := 1 + X + X ^ 2 + X ^ 3 + X ^ 4 with hXi
  set D : K := 1 + ω ^ 2 * σ z with hDdef
  have hX5 : X ^ 5 = (ω ^ 2 * σ z) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    have h1 : Gs ^ 5 = σ z • (1 : Matrix (Fin 5) (Fin 5) K) := by
      rw [hGs, ← conjTr_pow', hG, shiftZ_pow_five, conjTr_smul', conjTr_one]
    rw [hX, smul_pow, h1, smul_smul]
    congr 1
    linear_combination (ω ^ 2 * σ z) * hω3
  have hA'Xi : A' * Xi = D • (1 : Matrix (Fin 5) (Fin 5) K) := by
    rw [hA', hXi, geom_left h2, hX5, hDdef, add_smul, one_smul]
  have hXiA' : Xi * A' = D • (1 : Matrix (Fin 5) (Fin 5) K) := by
    rw [hA', hXi, geom_right h2, hX5, hDdef, add_smul, one_smul]
  have hGX : Commute G X := hcomm.smul_right ω
  have hAX : Commute A X := (Commute.one_left X).add_left ((hcomm.smul_left ω).smul_right ω)
  have hAA' : A * A' = A' * A := ((Commute.one_right A).add_right hAX).eq
  have hGA : Commute G A := (Commute.one_right G).add_right ((Commute.refl G).smul_right ω)
  have hGXi : Commute G Xi :=
    ((((Commute.one_right G).add_right hGX).add_right (hGX.pow_right 2)).add_right
      (hGX.pow_right 3)).add_right (hGX.pow_right 4)
  have hcA : conjTr σ A = A' := by
    rw [hA, hA', hX, conjTr_add, conjTr_one, conjTr_smul', hσω]
  have hcA' : conjTr σ A' = A := by
    rw [hA, hA', hX, conjTr_add, conjTr_one, conjTr_smul', hσω, hGs, conjTr_conjTr' σ hσ]
  have hcD : conjTr σ (D • (1 : Matrix (Fin 5) (Fin 5) K)) =
      σ D • (1 : Matrix (Fin 5) (Fin 5) K) := by
    rw [conjTr_smul', conjTr_one]
  have hXi'A : conjTr σ Xi * A = σ D • (1 : Matrix (Fin 5) (Fin 5) K) := by
    have := congrArg (conjTr σ) hA'Xi
    rw [conjTr_mul, hcA', hcD] at this
    exact this
  have hσD : σ D ≠ 0 := by simpa using hD
  set h1 : Matrix (Fin 5) (Fin 5) K := D⁻¹ • (A * Xi) with hh1
  have hu : conjTr σ h1 * h1 = 1 := by
    have e1 : conjTr σ h1 = (σ D)⁻¹ • (conjTr σ Xi * A') := by
      rw [hh1, conjTr_smul', conjTr_mul, hcA, map_inv₀]
    have e2 : conjTr σ Xi * A' * (A * Xi) = (σ D * D) • (1 : Matrix (Fin 5) (Fin 5) K) := by
      calc conjTr σ Xi * A' * (A * Xi) = conjTr σ Xi * (A' * A) * Xi := by
            simp only [Matrix.mul_assoc]
        _ = conjTr σ Xi * (A * A') * Xi := by rw [hAA']
        _ = (conjTr σ Xi * A) * (A' * Xi) := by simp only [Matrix.mul_assoc]
        _ = (σ D * D) • (1 : Matrix (Fin 5) (Fin 5) K) := by
          rw [hXi'A, hA'Xi, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    rw [e1, hh1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e2, smul_smul]
    have : (σ D)⁻¹ * D⁻¹ * (σ D * D) = 1 := by field_simp
    rw [this, one_smul]
  have hcommG : h1 * G = G * h1 := by
    have : Commute G h1 := (hGA.mul_right hGXi).smul_right _
    exact this.eq.symm
  have hD0 : D ≠ 0 := hD
  have hXiv : ∀ v w : Fin 5 → K, A' *ᵥ w = D • v → Xi *ᵥ v = w := by
    intro v w hvw
    have h1 : D • (Xi *ᵥ v) = D • w := by
      rw [← Matrix.mulVec_smul, ← hvw, Matrix.mulVec_mulVec, hXiA', Matrix.smul_mulVec,
        Matrix.one_mulVec]
    exact smul_right_injective _ hD0 h1
  have hA'v : ∀ w : Fin 5 → K, A' *ᵥ w = w + ω • ![w 1, w 2, w 3, w 4, σ z * w 0] := by
    intro w
    rw [hA', Matrix.add_mulVec, Matrix.one_mulVec, hX, Matrix.smul_mulVec, hGs, hG,
      conjTr_shiftZ_mulVec]
  have hAv : ∀ w : Fin 5 → K, A *ᵥ w = w + ω • ![z * w 4, w 0, w 1, w 2, w 3] := by
    intro w
    rw [hA, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hG, shiftZ_mulVec]
  have hw0 : A' *ᵥ ![0, ω * (σ z + ω), σ z + ω, ω ^ 2 * σ z + 1, 0] =
      D • ![1, 0, 0, 1, 0] := by
    rw [hA'v]
    ext i
    fin_cases i <;> simp [hDdef]
    · linear_combination hω3
    · linear_combination (ω * (σ z + ω)) * h2
    · linear_combination σ z * hω3 + (σ z + ω) * h2
    · ring
  have hXiu : Xi *ᵥ ![1, 0, 0, 1, 0] = ![0, ω * (σ z + ω), σ z + ω, ω ^ 2 * σ z + 1, 0] :=
    hXiv _ _ hw0
  have hAw0 : A *ᵥ ![0, ω * (σ z + ω), σ z + ω, ω ^ 2 * σ z + 1, 0] =
      (σ z + ω) • ![0, ω, ω, 1, 1] := by
    rw [hAv]
    ext i
    fin_cases i <;> simp
    · ring
    · linear_combination (σ z + ω) * hω - (ω * (σ z + ω)) * h2
    · linear_combination (σ z + 1) * hω - (σ z + ω) * h2
    · linear_combination σ z * hω3
  have hw1 : A' *ᵥ ![1, ω * σ z, σ z, ω ^ 2 * σ z, ω * σ z] = D • ![1, 0, 0, 0, 0] := by
    rw [hA'v]
    ext i
    fin_cases i <;> simp [hDdef]
    · ring
    · linear_combination (ω * σ z) * h2
    · linear_combination σ z * hω3 + σ z * h2
    · linear_combination (ω ^ 2 * σ z) * h2
    · linear_combination (ω * σ z) * h2
  have hXie : Xi *ᵥ ![1, 0, 0, 0, 0] = ![1, ω * σ z, σ z, ω ^ 2 * σ z, ω * σ z] := hXiv _ _ hw1
  have hAe : (A *ᵥ ![1, ω * σ z, σ z, ω ^ 2 * σ z, ω * σ z]) 0 = ω := by
    rw [hAv]
    simp
    linear_combination hω - ω * h2 + ω ^ 2 * hz
  have hh1v : ∀ v : Fin 5 → K, h1 *ᵥ v = D⁻¹ • (A *ᵥ (Xi *ᵥ v)) := by
    intro v
    rw [hh1, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hsz : σ z + ω ≠ 0 := by
    intro h
    apply hD0
    have : σ z = ω := by linear_combination h - ω * h2
    rw [hDdef, this]
    linear_combination hω3 + h2
  refine ⟨h1, D⁻¹ * ω, D⁻¹ * (σ z + ω), hu, hcommG, ?_, ?_, mul_ne_zero (inv_ne_zero hD0) hω0,
    mul_ne_zero (inv_ne_zero hD0) hsz⟩
  · rw [hh1v, hXiu, hAw0, smul_smul]
  · rw [hh1v, hXie]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hAe]

end CFSG.RankThree.PartOne.SEITZU49.Circ
