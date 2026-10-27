module

public import CFSG.RankThree.PartOne.KC.UnitaryCoordCentralizer
public import CFSG.RankThree.PartOne.KC.SemilinearTorusEigen

public section

namespace CFSG.RankThree.PartOne.KCUnitaryFrame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.RankThree.PartOne.KCGeneric

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem idForm_eq_dotProduct (x y : Fin n → K) :
    idForm h n x y = (fun k => h.bar (x k)) ⬝ᵥ y := by
  rw [gramForm_apply]
  simp [idGram]

@[expose] def IsOrthonormalFamily {ι : Type*} [DecidableEq ι] (b : ι → Fin n → K) : Prop :=
  ∀ i j, idForm h n (b i) (b j) = if i = j then 1 else 0

structure IsONPair (b₁ b₂ : Fin n → K) : Prop where
  self₁ : idForm h n b₁ b₁ = 1
  self₂ : idForm h n b₂ b₂ = 1
  cross₁₂ : idForm h n b₁ b₂ = 0
  cross₂₁ : idForm h n b₂ b₁ = 0

variable {h}

theorem IsOrthonormalFamily.pair {ι : Type*} [DecidableEq ι] {b : ι → Fin n → K}
    (hb : IsOrthonormalFamily h b) {i j : ι} (hij : i ≠ j) : IsONPair h (b i) (b j) where
  self₁ := by rw [hb i i, ite_eq_left rfl]
  self₂ := by rw [hb j j, ite_eq_left rfl]
  cross₁₂ := by rw [hb i j, ite_eq_right hij]
  cross₂₁ := by rw [hb j i, ite_eq_right hij.symm]

theorem IsOrthonormalFamily.linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → Fin n → K} (hb : IsOrthonormalFamily h b) : LinearIndependent K b := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (idForm h n (b j)) hc
  rw [map_sum, map_zero] at h1
  simp only [map_smul, hb j, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  simpa using h1

theorem IsOrthonormalFamily.linearIndependent_triple {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → Fin n → K} (hb : IsOrthonormalFamily h b) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : LinearIndependent K ![b i, b j, b k] := by
  have hinj : Function.Injective (![i, j, k] : Fin 3 → ι) := by
    intro a a' haa
    fin_cases a <;> fin_cases a' <;> simp_all
  have := hb.linearIndependent.comp ![i, j, k] hinj
  convert this using 1
  ext a
  fin_cases a <;> rfl

theorem IsONPair.linearIndependent {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) :
    LinearIndependent K ![b₁, b₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (idForm h n b₁) hst
  have h2 := congrArg (idForm h n b₂) hst
  simp only [map_add, map_smul, smul_eq_mul, hb.self₁, hb.cross₁₂, hb.cross₂₁, hb.self₂, mul_one,
    mul_zero, add_zero, zero_add, map_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem IsONPair.ne_zero_left {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) : b₁ ≠ 0 := by
  rintro rfl
  exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using hb.self₁)

variable (h)

@[expose] noncomputable def projMat (b : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.vecMulVec b (fun k => h.bar (b k))

theorem projMat_mulVec (b v : Fin n → K) : projMat h b *ᵥ v = idForm h n b v • b := by
  rw [projMat, Matrix.vecMulVec_mulVec, idForm_eq_dotProduct]
  simp

theorem projMat_mul_self {b : Fin n → K} (hb : idForm h n b b = 1) :
    projMat h b * projMat h b = projMat h b := by
  rw [projMat, Matrix.vecMulVec_mul_vecMulVec, ← idForm_eq_dotProduct, hb, one_smul]

theorem projMat_mul_of_orth {b b' : Fin n → K} (hb : idForm h n b b' = 0) :
    projMat h b * projMat h b' = 0 := by
  rw [projMat, projMat, Matrix.vecMulVec_mul_vecMulVec, ← idForm_eq_dotProduct, hb, zero_smul,
    Matrix.vecMulVec_zero]

theorem projMat_entry_bar (b : Fin n → K) (i j : Fin n) :
    h.bar (projMat h b j i) = projMat h b i j := by
  simp [projMat, Matrix.vecMulVec_apply, h.bar_bar, mul_comm]

@[expose] noncomputable def torusMat (b₁ b₂ : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + (c - 1) • projMat h b₁ + (c⁻¹ - 1) • projMat h b₂

theorem torusMat_one (b₁ b₂ : Fin n → K) : torusMat h b₁ b₂ 1 = 1 := by
  simp [torusMat]

theorem torusMat_mul {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) {c c' : K} :
    torusMat h b₁ b₂ c * torusMat h b₁ b₂ c' = torusMat h b₁ b₂ (c * c') := by
  have h11 := projMat_mul_self h hb.self₁
  have h22 := projMat_mul_self h hb.self₂
  have h12 := projMat_mul_of_orth h hb.cross₁₂
  have h21 := projMat_mul_of_orth h hb.cross₂₁
  unfold torusMat
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h11, h22, h12, h21, smul_zero, add_zero, mul_inv]
  module

theorem torusMat_mulVec (b₁ b₂ : Fin n → K) (c : K) (v : Fin n → K) :
    torusMat h b₁ b₂ c *ᵥ v = v + ((c - 1) * idForm h n b₁ v) • b₁ +
      ((c⁻¹ - 1) * idForm h n b₂ v) • b₂ := by
  unfold torusMat
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, projMat_mulVec, projMat_mulVec, smul_smul, smul_smul]

theorem torusMat_conjTranspose (b₁ b₂ : Fin n → K) (c : K) :
    ((torusMat h b₁ b₂ c).map h.bar)ᵀ =
      1 + (h.bar c - 1) • projMat h b₁ + (h.bar c⁻¹ - 1) • projMat h b₂ := by
  ext i j
  have e : h.bar ((1 : Matrix (Fin n) (Fin n) K) j i) = (1 : Matrix (Fin n) (Fin n) K) i j := by
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), map_zero]
  simp only [torusMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, projMat_entry_bar, e]

theorem torusMat_conjTranspose_of_norm (b₁ b₂ : Fin n → K) {c : K} (hn : h.norm c = 1) :
    ((torusMat h b₁ b₂ c).map h.bar)ᵀ = torusMat h b₁ b₂ c⁻¹ := by
  have hbar : h.bar c = c⁻¹ := by
    have : c * h.bar c = 1 := hn
    exact eq_inv_of_mul_eq_one_right this
  rw [torusMat_conjTranspose, torusMat]
  rw [hbar, map_inv₀, hbar, inv_inv]

theorem det_one_add_smul_projMat {b : Fin n → K} (hb : idForm h n b b = 1) (a : K) :
    (1 + a • projMat h b).det = 1 + a := by
  have h1 : a • projMat h b = Matrix.replicateCol Unit (a • b) *
      Matrix.replicateRow Unit (fun k => h.bar (b k)) := by
    rw [projMat, ← Matrix.vecMulVec_eq Unit, Matrix.smul_vecMulVec]
  rw [h1, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    ← idForm_eq_dotProduct, hb, smul_eq_mul, mul_one, add_comm]

theorem det_torusMat {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) {c : K} (hc : c ≠ 0) :
    (torusMat h b₁ b₂ c).det = 1 := by
  have h12 := projMat_mul_of_orth h hb.cross₁₂
  have hfac : torusMat h b₁ b₂ c =
      (1 + (c - 1) • projMat h b₁) * (1 + (c⁻¹ - 1) • projMat h b₂) := by
    unfold torusMat
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, h12, smul_zero, add_zero]
  rw [hfac, Matrix.det_mul, det_one_add_smul_projMat h hb.self₁,
    det_one_add_smul_projMat h hb.self₂]
  field_simp
  ring

@[expose] noncomputable def torusGL {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ) :
    GL (Fin n) K where
  val := torusMat h b₁ b₂ c
  inv := torusMat h b₁ b₂ ((c⁻¹ : Kˣ) : K)
  val_inv := by rw [torusMat_mul h hb, Units.mul_inv, torusMat_one]
  inv_val := by rw [torusMat_mul h hb, Units.inv_mul, torusMat_one]

theorem torusGL_mem {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) {c : Kˣ}
    (hc : h.norm (c : K) = 1) : torusGL h hb c ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  change ((torusMat h b₁ b₂ c).map h.bar)ᵀ * torusMat h b₁ b₂ c = 1
  rw [torusMat_conjTranspose_of_norm h b₁ b₂ hc, torusMat_mul h hb, inv_mul_cancel₀ c.ne_zero,
    torusMat_one]

@[expose] noncomputable def torusUnitary {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) : primeFormUnitary h (idGram K n) :=
  ⟨torusGL h hb c, torusGL_mem h hb hc⟩

theorem coe_torusUnitary {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) :
    (((torusUnitary h hb c hc : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = torusMat h b₁ b₂ c := rfl

theorem det_torusUnitary {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : Kˣ)
    (hc : h.norm (c : K) = 1) :
    (((torusUnitary h hb c hc : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 :=
  det_torusMat h hb c.ne_zero

@[expose] noncomputable def semilinRep (M : Matrix (Fin n) (Fin n) K) (τ : K →+* K) :
    (Fin n → K) →ₛₗ[τ] (Fin n → K) where
  toFun v := M *ᵥ fun i => τ (v i)
  map_add' u v := by
    have : (fun i => τ ((u + v) i)) = (fun i => τ (u i)) + fun i => τ (v i) := by
      ext i
      simp
    rw [this, Matrix.mulVec_add]
  map_smul' c v := by
    have : (fun i => τ ((c • v) i)) = τ c • fun i => τ (v i) := by
      ext i
      simp
    rw [this, Matrix.mulVec_smul]

theorem semilinRep_apply (M : Matrix (Fin n) (Fin n) K) (τ : K →+* K) (v : Fin n → K) :
    semilinRep M τ v = M *ᵥ fun i => τ (v i) := rfl

theorem semilinRep_injective {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M) (τ : K →+* K) :
    Function.Injective (semilinRep M τ) := by
  intro u v huv
  rw [semilinRep_apply, semilinRep_apply] at huv
  have h1 := Matrix.mulVec_injective_iff_isUnit.mpr hM huv
  ext i
  exact τ.injective (congrFun h1 i)

theorem semilinRep_mulVec_comm {M Y : Matrix (Fin n) (Fin n) K} (τ : K →+* K)
    (hY : M * Y.map τ = Y * M) (v : Fin n → K) :
    semilinRep M τ (Y *ᵥ v) = Y *ᵥ semilinRep M τ v := by
  rw [semilinRep_apply, semilinRep_apply]
  have : (fun i => τ ((Y *ᵥ v) i)) = Y.map τ *ᵥ fun i => τ (v i) := by
    ext i
    exact RingHom.map_mulVec τ Y v i
  rw [this, Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec]

theorem torus_range_mem_span (b₁ b₂ : Fin n → K) (c : K) (v : Fin n → K) :
    torusMat h b₁ b₂ c *ᵥ v - v ∈ Submodule.span K {b₁, b₂} := by
  rw [torusMat_mulVec, add_assoc, add_sub_cancel_left]
  exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩

theorem torus_apply_first {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : K) :
    torusMat h b₁ b₂ c *ᵥ b₁ = c • b₁ := by
  rw [torusMat_mulVec, hb.self₁, hb.cross₂₁, mul_zero, zero_smul, add_zero, mul_one, sub_smul,
    one_smul]
  abel

theorem torus_apply_second {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : K) :
    torusMat h b₁ b₂ c *ᵥ b₂ = c⁻¹ • b₂ := by
  rw [torusMat_mulVec, hb.self₂, hb.cross₁₂, mul_zero, zero_smul, add_zero, mul_one,
    sub_smul, one_smul]
  abel

theorem tau_eq_one_of_torus {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M) {τ : K ≃+* K}
    {b₁ b₂ b₃ : Fin n → K} (h12 : IsONPair h b₁ b₂) (h13 : IsONPair h b₁ b₃)
    (hind : LinearIndependent K ![b₁, b₂, b₃])
    (hY₂ : ∀ c : Kˣ, h.norm (c : K) = 1 →
      M * (torusMat h b₁ b₂ c).map τ = torusMat h b₁ b₂ c * M)
    (hY₃ : ∀ c : Kˣ, h.norm (c : K) = 1 →
      M * (torusMat h b₁ b₃ c).map τ = torusMat h b₁ b₃ c * M) :
    τ = RingEquiv.refl K := by
  refine eq_one_of_fixes_norm_one h τ fun v hv => ?_
  by_cases hv1 : (v : K) = 1
  · rw [hv1, map_one]
  by_cases hvv : (v : K) = (v : K)⁻¹
  · have h2 : ((v : K) - 1) * ((v : K) + 1) = 0 := by
      have h3 : (v : K) * (v : K) = 1 := by
        calc (v : K) * (v : K) = (v : K) * (v : K)⁻¹ := by rw [← hvv]
          _ = 1 := mul_inv_cancel₀ v.ne_zero
      linear_combination h3
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hv1
    · have h4 : (v : K) = -1 := eq_neg_of_add_eq_zero_left h3
      rw [h4, map_neg, map_one]
  · have hτ1 : (τ : K →+* K) (v : K) ≠ 1 := by
      intro h1
      apply hv1
      exact τ.injective (by rw [map_one]; exact h1)
    refine semilinear_fixes_of_torus_triple (semilinRep M (τ : K →+* K))
      (semilinRep_injective hM _) hind (Matrix.toLin' (torusMat h b₁ b₂ v))
      (Matrix.toLin' (torusMat h b₁ b₃ v)) (c := (v : K)) (c₂ := (v : K)⁻¹)
      (c₃ := (v : K)⁻¹) (fun w => ?_) (fun w => ?_) ?_ ?_ ?_ ?_ hvv hvv hτ1 (fun w => ?_)
      (fun w => ?_)
    · rw [Matrix.toLin'_apply]
      exact torus_range_mem_span h b₁ b₂ _ w
    · rw [Matrix.toLin'_apply]
      exact torus_range_mem_span h b₁ b₃ _ w
    · rw [Matrix.toLin'_apply]
      exact torus_apply_first h h12 _
    · rw [Matrix.toLin'_apply]
      exact torus_apply_second h h12 _
    · rw [Matrix.toLin'_apply]
      exact torus_apply_first h h13 _
    · rw [Matrix.toLin'_apply]
      exact torus_apply_second h h13 _
    · simp only [Matrix.toLin'_apply]
      exact semilinRep_mulVec_comm _ (hY₂ v hv) w
    · simp only [Matrix.toLin'_apply]
      exact semilinRep_mulVec_comm _ (hY₃ v hv) w

end CFSG.RankThree.PartOne.KCUnitaryFrame
