module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n : ℕ}

section Algebra

variable [CharP K 2] (i₀ i₁ i₂ : Fin n)

@[expose] def vvec : Fin n → K := Pi.single i₀ 1 + Pi.single i₁ 1

@[expose] def uvec : Fin n → K := Pi.single i₂ 1

@[expose] def Nrad (α β γ : K) : Matrix (Fin n) (Fin n) K :=
  vecMulVec (vvec i₀ i₁ : Fin n → K) (α • (vvec i₀ i₁ : Fin n → K) + γ • (uvec i₂ : Fin n → K)) +
    vecMulVec (uvec i₂ : Fin n → K) (β • (vvec i₀ i₁ : Fin n → K))

variable {i₀ i₁ i₂}

theorem vvec_dot_vvec (h01 : i₀ ≠ i₁) : (vvec i₀ i₁ : Fin n → K) ⬝ᵥ vvec i₀ i₁ = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [vvec, dotProduct_add, dotProduct_single, h01, h01.symm]
  linear_combination h2

omit [CharP K 2] in
theorem vvec_dot_uvec (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    (vvec i₀ i₁ : Fin n → K) ⬝ᵥ uvec i₂ = 0 := by
  simp [vvec, uvec, dotProduct_single, h02, h12]

omit [CharP K 2] in
theorem uvec_dot_vvec (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    (uvec i₂ : Fin n → K) ⬝ᵥ vvec i₀ i₁ = 0 := by
  rw [dotProduct_comm]
  exact vvec_dot_uvec h02 h12

omit [CharP K 2] in
theorem uvec_dot_uvec : (uvec i₂ : Fin n → K) ⬝ᵥ uvec i₂ = 1 := by
  simp [uvec]

omit [CharP K 2] in
theorem Nrad_add (α β γ α' β' γ' : K) :
    Nrad i₀ i₁ i₂ α β γ + Nrad i₀ i₁ i₂ α' β' γ' =
      Nrad i₀ i₁ i₂ (α + α') (β + β') (γ + γ') := by
  simp only [Nrad, add_smul, vecMulVec_add]
  abel

omit [CharP K 2] in
theorem Nrad_zero : Nrad i₀ i₁ i₂ (0 : K) 0 0 = 0 := by
  simp [Nrad]

theorem Nrad_mul (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ α' β' γ' : K) :
    Nrad i₀ i₁ i₂ α β γ * Nrad i₀ i₁ i₂ α' β' γ' = Nrad i₀ i₁ i₂ (γ * β') 0 0 := by
  have hvv := vvec_dot_vvec (K := K) h01
  have hvu := vvec_dot_uvec (K := K) h02 h12
  have huv := uvec_dot_vvec (K := K) h02 h12
  have huu := uvec_dot_uvec (K := K) (i₂ := i₂)
  simp only [Nrad, add_mul, mul_add, vecMulVec_mul_vecMulVec, add_dotProduct, smul_dotProduct,
    hvv, hvu, huv, huu, smul_eq_mul, mul_zero, add_zero, zero_add, zero_smul, mul_one,
    smul_add, vecMulVec_zero]
  simp [vecMulVec_smul, smul_smul]

end Algebra

section Group

variable [CharP K 2] (i₀ i₁ i₂ : Fin n) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)

theorem one_add_Nrad_mul {i₀ i₁ i₂ : Fin n} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (α β γ α' β' γ' : K) :
    (1 + Nrad i₀ i₁ i₂ α β γ) * (1 + Nrad i₀ i₁ i₂ α' β' γ') =
      1 + Nrad i₀ i₁ i₂ (α + α' + γ * β') (β + β') (γ + γ') := by
  have hm := Nrad_mul h01 h02 h12 α β γ α' β' γ'
  have ha := Nrad_add (i₀ := i₀) (i₁ := i₁) (i₂ := i₂) α β γ α' β' γ'
  have hb := Nrad_add (i₀ := i₀) (i₁ := i₁) (i₂ := i₂) (α + α') (β + β') (γ + γ') (γ * β') 0 0
  simp only [add_zero] at hb
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hm]
  rw [← hb, ← ha]
  abel

include h01 h02 h12 in
@[expose] def radH : Subgroup (GL (Fin n) K) where
  carrier := {g | ∃ α β γ : K, (g : Matrix (Fin n) (Fin n) K) = 1 + Nrad i₀ i₁ i₂ α β γ}
  mul_mem' := by
    rintro g g' ⟨α, β, γ, hg⟩ ⟨α', β', γ', hg'⟩
    refine ⟨α + α' + γ * β', β + β', γ + γ', ?_⟩
    rw [Units.val_mul, hg, hg', one_add_Nrad_mul h01 h02 h12]
  one_mem' := ⟨0, 0, 0, by simp [Nrad_zero]⟩
  inv_mem' := by
    rintro g ⟨α, β, γ, hg⟩
    refine ⟨α + γ * β, β, γ, ?_⟩
    have hprod : (g : Matrix (Fin n) (Fin n) K) * (1 + Nrad i₀ i₁ i₂ (α + γ * β) β γ) = 1 := by
      rw [hg, one_add_Nrad_mul h01 h02 h12]
      have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
      have e1 : α + (α + γ * β) + γ * β = 0 := by
        calc α + (α + γ * β) + γ * β = (α + α) + (γ * β + γ * β) := by ring
          _ = 0 := by rw [h2, h2, add_zero]
      simp only [e1, h2, add_zero, Nrad_zero]
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : Matrix (Fin n) (Fin n) K) * (1 + Nrad i₀ i₁ i₂ (α + γ * β) β γ)) := by
          rw [hprod, Matrix.mul_one]
      _ = 1 + Nrad i₀ i₁ i₂ (α + γ * β) β γ := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]

theorem Nrad_cube (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ : K) :
    Nrad i₀ i₁ i₂ α β γ * Nrad i₀ i₁ i₂ α β γ * Nrad i₀ i₁ i₂ α β γ = 0 := by
  rw [Nrad_mul h01 h02 h12, Nrad_mul h01 h02 h12]
  simp [Nrad_zero]

theorem radH_pow_four (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) {g : GL (Fin n) K}
    (hg : g ∈ radH i₀ i₁ i₂ h01 h02 h12) : g ^ 4 = 1 := by
  obtain ⟨α, β, γ, hg⟩ := hg
  apply Units.ext
  have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have hg2 : ((g : Matrix (Fin n) (Fin n) K)) ^ 2 = 1 + Nrad i₀ i₁ i₂ (γ * β) 0 0 := by
    rw [pow_two, hg, one_add_Nrad_mul h01 h02 h12]
    simp only [h2, zero_add]
  rw [Units.val_pow_eq_pow_val, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg2, pow_two,
    one_add_Nrad_mul h01 h02 h12, Units.val_one]
  simp only [h2, mul_zero, add_zero, Nrad_zero]

end Group

section Conj

variable {i₀ i₁ i₂ : Fin n}

theorem diagU_inv_val (d : Fin n → Kˣ) :
    (((diagU d)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K) := by
  have : (diagU d)⁻¹ = diagU (d⁻¹) := by
    rw [inv_eq_iff_mul_eq_one, diagU_mul, mul_inv_cancel, diagU_one]
  rw [this, diagU_val]
  rfl

theorem diag_mulVec_vvec (h01 : i₀ ≠ i₁) (d : Fin n → Kˣ) (hd : d i₀ = d i₁) :
    (Matrix.diagonal fun i => (d i : K)) *ᵥ (vvec i₀ i₁ : Fin n → K) =
      (d i₀ : K) • (vvec i₀ i₁ : Fin n → K) := by
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, vvec, Pi.add_apply,
    Pi.single_apply]
  by_cases h0 : i = i₀
  · subst h0
    simp [h01]
  · by_cases h1 : i = i₁
    · subst h1
      simp [h0, hd]
    · simp [h0, h1]

theorem diag_mulVec_uvec (d : Fin n → Kˣ) :
    (Matrix.diagonal fun i => (d i : K)) *ᵥ (uvec i₂ : Fin n → K) =
      (d i₂ : K) • (uvec i₂ : Fin n → K) := by
  funext i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, uvec, Pi.single_apply]
  by_cases h : i = i₂
  · subst h
    simp
  · simp [h]

theorem vvec_vecMul_diag (h01 : i₀ ≠ i₁) (d : Fin n → Kˣ) (hd : d i₀ = d i₁) :
    (vvec i₀ i₁ : Fin n → K) ᵥ* (Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)) =
      (((d i₀)⁻¹ : Kˣ) : K) • (vvec i₀ i₁ : Fin n → K) := by
  funext i
  simp only [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul, vvec, Pi.add_apply,
    Pi.single_apply]
  by_cases h0 : i = i₀
  · subst h0
    simp [h01]
  · by_cases h1 : i = i₁
    · subst h1
      simp [h0, hd]
    · simp [h0, h1]

theorem uvec_vecMul_diag (d : Fin n → Kˣ) :
    (uvec i₂ : Fin n → K) ᵥ* (Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)) =
      (((d i₂)⁻¹ : Kˣ) : K) • (uvec i₂ : Fin n → K) := by
  funext i
  simp only [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul, uvec, Pi.single_apply]
  by_cases h : i = i₂
  · subst h
    simp
  · simp [h]

theorem diag_conj_Nrad (h01 : i₀ ≠ i₁) (d : Fin n → Kˣ) (hd : d i₀ = d i₁) (α β γ : K) :
    (Matrix.diagonal fun i => (d i : K)) * Nrad i₀ i₁ i₂ α β γ *
        (Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)) =
      Nrad i₀ i₁ i₂ α (β * ((d i₂ : K) * (((d i₀)⁻¹ : Kˣ) : K)))
        (γ * ((d i₀ : K) * (((d i₂)⁻¹ : Kˣ) : K))) := by
  have hv1 := diag_mulVec_vvec (K := K) h01 d hd
  have hu1 := diag_mulVec_uvec (K := K) (i₂ := i₂) d
  have hv2 := vvec_vecMul_diag (K := K) h01 d hd
  have hu2 := uvec_vecMul_diag (K := K) (i₂ := i₂) d
  have e0 : (d i₀ : K) * (((d i₀)⁻¹ : Kˣ) : K) = 1 := by simp
  have e2 : (d i₂ : K) * (((d i₂)⁻¹ : Kˣ) : K) = 1 := by simp
  unfold Nrad
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hv1, hu1, Matrix.add_vecMul, Matrix.smul_vecMul,
    Matrix.smul_vecMul, Matrix.smul_vecMul, hv2, hu2]
  simp only [vecMulVec_add, vecMulVec_smul, smul_vecMulVec, smul_smul]
  have c1 : α * (((d i₀)⁻¹ : Kˣ) : K) * (d i₀ : K) = α := by linear_combination α * e0
  have c2 : γ * (((d i₂)⁻¹ : Kˣ) : K) * (d i₀ : K) =
      γ * ((d i₀ : K) * (((d i₂)⁻¹ : Kˣ) : K)) := by ring
  have c3 : β * (((d i₀)⁻¹ : Kˣ) : K) * (d i₂ : K) =
      β * ((d i₂ : K) * (((d i₀)⁻¹ : Kˣ) : K)) := by ring
  rw [c1, c2, c3]

theorem Nrad_apply_i0_i2 (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ : K) :
    Nrad i₀ i₁ i₂ α β γ i₀ i₂ = γ := by
  simp [Nrad, vecMulVec_apply, vvec, uvec, h01, h02, h02.symm, h12.symm]

end Conj

section Elements

variable [CharP K 2] {i₀ i₁ i₂ : Fin n}

@[expose] def mkRad (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ : K) :
    GL (Fin n) K where
  val := 1 + Nrad i₀ i₁ i₂ α β γ
  inv := 1 + Nrad i₀ i₁ i₂ (α + γ * β) β γ
  val_inv := by
    have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
    rw [one_add_Nrad_mul h01 h02 h12]
    have e1 : α + (α + γ * β) + γ * β = 0 := by
      calc α + (α + γ * β) + γ * β = (α + α) + (γ * β + γ * β) := by ring
        _ = 0 := by rw [h2, h2, add_zero]
    simp only [e1, h2, Nrad_zero, add_zero]
  inv_val := by
    have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
    rw [one_add_Nrad_mul h01 h02 h12]
    have e1 : α + γ * β + α + γ * (β) = 0 := by
      calc α + γ * β + α + γ * β = (α + α) + (γ * β + γ * β) := by ring
        _ = 0 := by rw [h2, h2, add_zero]
    simp only [e1, h2, Nrad_zero, add_zero]

theorem coe_mkRad (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ : K) :
    ((mkRad h01 h02 h12 α β γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + Nrad i₀ i₁ i₂ α β γ := rfl

theorem mkRad_mem (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (α β γ : K) :
    mkRad h01 h02 h12 α β γ ∈ radH i₀ i₁ i₂ h01 h02 h12 := ⟨α, β, γ, rfl⟩

theorem coe_diagU_conj_mkRad (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (d : Fin n → Kˣ)
    (hd : d i₀ = d i₁) (α β γ : K) :
    ((diagU d * mkRad h01 h02 h12 α β γ * (diagU d)⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      1 + Nrad i₀ i₁ i₂ α (β * ((d i₂ : K) * (((d i₀)⁻¹ : Kˣ) : K)))
        (γ * ((d i₀ : K) * (((d i₂)⁻¹ : Kˣ) : K))) := by
  have hDD : (Matrix.diagonal fun i => (d i : K)) *
      (Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (d i : K) * (((d i)⁻¹ : Kˣ) : K)) = fun _ => 1 := funext fun i => by simp
    rw [this, Matrix.diagonal_one]
  rw [Units.val_mul, Units.val_mul, diagU_inv_val, diagU_val, coe_mkRad, mul_add, add_mul,
    Matrix.mul_one, hDD, diag_conj_Nrad h01 d hd]

theorem diagU_conj_mem_radH (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (d : Fin n → Kˣ)
    (hd : d i₀ = d i₁) {g : GL (Fin n) K} (hg : g ∈ radH i₀ i₁ i₂ h01 h02 h12) :
    diagU d * g * (diagU d)⁻¹ ∈ radH i₀ i₁ i₂ h01 h02 h12 := by
  obtain ⟨α, β, γ, hg⟩ := hg
  have : g = mkRad h01 h02 h12 α β γ := Units.ext hg
  subst this
  exact ⟨α, β * ((d i₂ : K) * (((d i₀)⁻¹ : Kˣ) : K)),
    γ * ((d i₀ : K) * (((d i₂)⁻¹ : Kˣ) : K)), coe_diagU_conj_mkRad h01 h02 h12 d hd α β γ⟩

theorem diagU_conj_mkRad_ne (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) (d : Fin n → Kˣ)
    (hd : d i₀ = d i₁) (hne : d i₀ ≠ d i₂) (α : K) :
    diagU d * mkRad h01 h02 h12 α 1 1 * (diagU d)⁻¹ ≠ mkRad h01 h02 h12 α 1 1 := by
  intro heq
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₀ i₂) heq
  simp only [coe_diagU_conj_mkRad h01 h02 h12 d hd, coe_mkRad, Matrix.add_apply,
    Nrad_apply_i0_i2 h01 h02 h12, Matrix.one_apply_ne h02] at h1
  apply hne
  have h2 : ((d i₀ : Kˣ) : K) * (((d i₂)⁻¹ : Kˣ) : K) = 1 := by simpa using h1
  have h3 : ((d i₀ : Kˣ) : K) = (d i₂ : K) := by
    have := congrArg (fun x : K => x * (d i₂ : K)) h2
    simpa [mul_assoc] using this
  exact Units.ext h3

end Elements

section Unitary

variable {f : ℕ} {i₀ i₁ i₂ : Fin n}

theorem bar_vvec (h : UnitaryFieldData 2 f K) (i : Fin n) :
    h.bar (vvec i₀ i₁ i : K) = vvec i₀ i₁ i := by
  simp [vvec, Pi.single_apply, apply_ite h.bar]

theorem bar_uvec (h : UnitaryFieldData 2 f K) (i : Fin n) :
    h.bar (uvec i₂ i : K) = uvec i₂ i := by
  simp [uvec, Pi.single_apply, apply_ite h.bar]

theorem conjT_Nrad (h : UnitaryFieldData 2 f K) (α β γ : K) :
    ((Nrad i₀ i₁ i₂ α β γ).map h.bar)ᵀ =
      vecMulVec (h.bar α • (vvec i₀ i₁ : Fin n → K) + h.bar γ • (uvec i₂ : Fin n → K))
        (vvec i₀ i₁) +
        vecMulVec (h.bar β • (vvec i₀ i₁ : Fin n → K)) (uvec i₂) := by
  ext i j
  have hvi := bar_vvec (i₀ := i₀) (i₁ := i₁) h i
  have hvj := bar_vvec (i₀ := i₀) (i₁ := i₁) h j
  have hui := bar_uvec (i₂ := i₂) h i
  have huj := bar_uvec (i₂ := i₂) h j
  simp only [Nrad, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hvi, hvj, hui, huj]
  ring

theorem one_add_Nrad_unitary [CharP K 2] (h : UnitaryFieldData 2 f K) (h01 : i₀ ≠ i₁)
    (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) {α β γ : K} (hαβ : α + h.bar α = h.bar β * β)
    (hγ : γ = h.bar β) :
    (((1 + Nrad i₀ i₁ i₂ α β γ : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ *
      (1 + Nrad i₀ i₁ i₂ α β γ) = 1 := by
  have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have hvv := vvec_dot_vvec (K := K) h01
  have hvu := vvec_dot_uvec (K := K) h02 h12
  have huv := uvec_dot_vvec (K := K) h02 h12
  have huu := uvec_dot_uvec (K := K) (i₂ := i₂)
  have hT := conjT_Nrad (i₀ := i₀) (i₁ := i₁) (i₂ := i₂) h α β γ
  rw [Matrix.map_add h.bar (map_add h.bar), Matrix.transpose_add,
    Matrix.map_one h.bar (map_zero _) (map_one _),
    Matrix.transpose_one, hT]
  have hprod :
      (vecMulVec (h.bar α • (vvec i₀ i₁ : Fin n → K) + h.bar γ • (uvec i₂ : Fin n → K))
          (vvec i₀ i₁) + vecMulVec (h.bar β • (vvec i₀ i₁ : Fin n → K)) (uvec i₂)) *
        Nrad i₀ i₁ i₂ α β γ = vecMulVec (h.bar β • (vvec i₀ i₁ : Fin n → K))
          (β • (vvec i₀ i₁ : Fin n → K)) := by
    unfold Nrad
    simp only [add_mul, mul_add, vecMulVec_mul_vecMulVec, hvv, hvu, huv, huu, zero_smul,
      one_smul, vecMulVec_zero, add_zero, zero_add]
  generalize hX : (vecMulVec (h.bar α • (vvec i₀ i₁ : Fin n → K) +
    h.bar γ • (uvec i₂ : Fin n → K)) (vvec i₀ i₁) +
      vecMulVec (h.bar β • (vvec i₀ i₁ : Fin n → K)) (uvec i₂)) = X at hprod ⊢
  have hexp : (1 + X) * (1 + Nrad i₀ i₁ i₂ α β γ) =
      1 + X + Nrad i₀ i₁ i₂ α β γ + X * Nrad i₀ i₁ i₂ α β γ := by
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hexp, hprod]
  have hbb : h.bar (h.bar β) = β := h.bar_bar β
  have hγb : h.bar γ = β := by rw [hγ, hbb]
  rw [← hX]
  unfold Nrad
  simp only [vecMulVec_add, add_vecMulVec, vecMulVec_smul, smul_vecMulVec, smul_smul, hγb]
  have c1 : α + h.bar α + h.bar β * β = 0 := by rw [hαβ, h2]
  have c2 : γ + h.bar β = 0 := by rw [hγ, h2]
  have c3 : β + β = 0 := h2 β
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : h.bar α + α + β * h.bar β = 0 := by
    linear_combination hαβ + (β * h.bar β) * two
  have hc2 : h.bar β + γ = 0 := by rw [hγ, h2]
  have e : (1 : Matrix (Fin n) (Fin n) K) +
      (h.bar α • vecMulVec (vvec i₀ i₁) (vvec i₀ i₁) + β • vecMulVec (uvec i₂) (vvec i₀ i₁) +
        h.bar β • vecMulVec (vvec i₀ i₁) (uvec i₂)) +
      (α • vecMulVec (vvec i₀ i₁) (vvec i₀ i₁) + γ • vecMulVec (vvec i₀ i₁) (uvec i₂) +
        β • vecMulVec (uvec i₂) (vvec i₀ i₁)) +
      (β * h.bar β) • vecMulVec (vvec i₀ i₁) (vvec i₀ i₁) =
      1 + ((h.bar α + α + β * h.bar β) • vecMulVec (vvec i₀ i₁) (vvec i₀ i₁) +
        (h.bar β + γ) • vecMulVec (vvec i₀ i₁) (uvec i₂) +
        (β + β) • vecMulVec (uvec i₂) (vvec i₀ i₁)) := by
    module
  rw [e, hc1, hc2, c3]
  simp

theorem det_one_add_Nrad [CharP K 2] (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (α β γ : K) : (1 + Nrad i₀ i₁ i₂ α β γ).det = 1 :=
  CFSG.LieType.BorelTits.det_one_add_of_isNilpotent 2
    ⟨3, by rw [pow_succ, pow_two]; exact Nrad_cube i₀ i₁ i₂ h01 h02 h12 α β γ⟩

theorem mkRad_mem_unitarySU [CharP K 2] (h : UnitaryFieldData 2 f K) (h01 : i₀ ≠ i₁)
    (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) {α β γ : K} (hαβ : α + h.bar α = h.bar β * β)
    (hγ : γ = h.bar β) : mkRad h01 h02 h12 α β γ ∈ unitarySU 2 f K n :=
  (mem_unitarySU_iff h).2 ⟨det_one_add_Nrad h01 h02 h12 α β γ,
    one_add_Nrad_unitary h h01 h02 h12 hαβ hγ⟩

theorem exists_trace_one [CharP K 2] (h : UnitaryFieldData 2 f K) : ∃ a : K, a + h.bar a = 1 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : c + h.bar c ≠ 0 := by
    intro h0
    apply hc
    linear_combination h0 - c * two
  refine ⟨c / (c + h.bar c), ?_⟩
  have hfix : h.bar (c + h.bar c) = c + h.bar c := by
    rw [map_add, h.bar_bar, add_comm]
  rw [map_div₀, hfix]
  field_simp

end Unitary

end CFSG.RankThree.PartOne.KFU
