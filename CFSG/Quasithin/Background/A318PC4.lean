module

public import CFSG.Quasithin.Background.A318PC2

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial
open Matrix Polynomial

section Linear

variable {K : Type} [Field K]

theorem not_irreducible_of_eigenvector {y : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K}
    (hv : v ≠ 0) {c : K} (hyv : y *ᵥ v = c • v)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ w ∈ W, y *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) : False := by
  rcases hirr (K ∙ v) (fun w hw => by
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [Matrix.mulVec_smul, hyv]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
    with h | h
  · exact hv ((Submodule.span_singleton_eq_bot).1 h)
  · have := finrank_span_singleton (K := K) hv
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega

theorem not_cube_of_irreducible {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {y : Matrix (Fin 3) (Fin 3) K} {ℓ : K} (hy : y ^ 3 = ℓ • 1)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ w ∈ W, y *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ μ : K, μ ^ 3 ≠ ℓ := by
  intro μ hμ
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
  have hpoly : ((X - C μ) * (X - C (μ * τ)) * (X - C (μ * τ ^ 2)) : K[X]) = X ^ 3 - C ℓ := by
    rw [← hμ]
    simp only [map_mul, map_pow]
    have hsC : (1 + C τ + C τ ^ 2 : K[X]) = 0 := by
      have := congrArg (C : K →+* K[X]) hs
      simpa using this
    have ht3 : (C τ : K[X]) ^ 3 = 1 := by
      have := congrArg (C : K →+* K[X]) hτ
      simpa using this
    linear_combination (-(C μ * X ^ 2) + C μ ^ 2 * X) * hsC + (C μ ^ 2 * X - C μ ^ 3) * ht3
  have hy0 : aeval y ((X - C μ) * (X - C (μ * τ)) * (X - C (μ * τ ^ 2)) : K[X]) = 0 := by
    rw [hpoly, map_sub, map_pow, aeval_X, aeval_C, hy, Algebra.algebraMap_eq_smul_one, sub_self]
  rw [map_mul, map_mul] at hy0
  simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hy0
  have hdet := congrArg Matrix.det hy0
  rw [det_mul, det_mul, det_zero] at hdet
  rcases mul_eq_zero.mp hdet with h | h
  · rcases mul_eq_zero.mp h with h | h
    · obtain ⟨v, hv, hyv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
      refine not_irreducible_of_eigenvector hv (c := μ) ?_ hirr
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hyv
      exact hyv
    · obtain ⟨v, hv, hyv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
      refine not_irreducible_of_eigenvector hv (c := μ * τ) ?_ hirr
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hyv
      exact hyv
  · obtain ⟨v, hv, hyv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine not_irreducible_of_eigenvector hv (c := μ * τ ^ 2) ?_ hirr
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hyv
    exact hyv

theorem exists_conj_gl {y₁ y₂ : GL (Fin 3) K} {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (h₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    (h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ P : GL (Fin 3) K, (P : Matrix (Fin 3) (Fin 3) K) * y₁ = y₂ * P := by
  set v : Fin 3 → K := Pi.single 0 1 with hvdef
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hvdef] at this
  have hP₁ := isUnit_colMat (linearIndependent_cyclic hℓ h₁ hv)
  have hP₂ := isUnit_colMat (linearIndependent_cyclic hℓ h₂ hv)
  have e₁ := mul_colMat_cyclic h₁ v
  have e₂ := mul_colMat_cyclic h₂ v
  set B₁ := colMat ![v, (y₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
    ((y₁ : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v] with hB₁
  set B₂ := colMat ![v, (y₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
    ((y₂ : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v] with hB₂
  obtain ⟨U₁, hU₁⟩ := hP₁
  obtain ⟨U₂, hU₂⟩ := hP₂
  refine ⟨U₂ * U₁⁻¹, ?_⟩
  rw [Units.val_mul]
  set I₁ : Matrix (Fin 3) (Fin 3) K := ((U₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hI₁
  have hI₁r : (U₁ : Matrix (Fin 3) (Fin 3) K) * I₁ = 1 := Units.mul_inv U₁
  have hI₁l : I₁ * (U₁ : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul U₁
  have h₁' : (y₁ : Matrix (Fin 3) (Fin 3) K) * U₁ = U₁ * companionThree ℓ := by
    rw [hU₁]
    exact e₁
  have h₂' : (y₂ : Matrix (Fin 3) (Fin 3) K) * U₂ = U₂ * companionThree ℓ := by
    rw [hU₂]
    exact e₂
  have hy₁ : I₁ * (y₁ : Matrix (Fin 3) (Fin 3) K) = companionThree ℓ * I₁ := by
    calc I₁ * (y₁ : Matrix (Fin 3) (Fin 3) K)
        = I₁ * (y₁ : Matrix (Fin 3) (Fin 3) K) * (U₁ * I₁) := by rw [hI₁r, Matrix.mul_one]
      _ = I₁ * ((y₁ : Matrix (Fin 3) (Fin 3) K) * U₁) * I₁ := by simp only [Matrix.mul_assoc]
      _ = I₁ * (U₁ * companionThree ℓ) * I₁ := by rw [h₁']
      _ = (I₁ * U₁) * companionThree ℓ * I₁ := by simp only [Matrix.mul_assoc]
      _ = companionThree ℓ * I₁ := by rw [hI₁l, Matrix.one_mul]
  calc (U₂ : Matrix (Fin 3) (Fin 3) K) * I₁ * y₁ =
      U₂ * (I₁ * y₁) := Matrix.mul_assoc _ _ _
    _ = U₂ * (companionThree ℓ * I₁) := by rw [hy₁]
    _ = (U₂ * companionThree ℓ) * I₁ := (Matrix.mul_assoc _ _ _).symm
    _ = (y₂ * U₂) * I₁ := by rw [h₂']
    _ = y₂ * (U₂ * I₁) := Matrix.mul_assoc _ _ _

end Linear

section Unitary

variable {K : Type} [Field K] {p f : ℕ}

theorem exists_conj_gu (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {y₁ y₂ : GL (Fin 3) K} (hH₁ : y₁ ∈ glPi false 3 (p ^ f) K) (hH₂ : y₂ ∈ glPi false 3 (p ^ f) K)
    {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (h₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    (h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ P : GL (Fin 3) K, P ∈ glPi false 3 (p ^ f) K ∧
      (P : Matrix (Fin 3) (Fin 3) K) * y₁ = y₂ * P := by
  have h := hK.unitary
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  have h3 := unitaryFieldData_cubeField hK ℓ
  have key := cubeHom_bar hK hq hH₁ hℓ h₁ h3
  have ct_mul : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      ((A * B).map h.bar)ᵀ = (B.map h.bar)ᵀ * (A.map h.bar)ᵀ := fun A B => by
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have ct_ct : ∀ A : Matrix (Fin 3) (Fin 3) K, (((A.map h.bar)ᵀ).map h.bar)ᵀ = A := fun A => by
    ext i j
    simp [h.bar_bar]
  set Y₁ := (y₁ : Matrix (Fin 3) (Fin 3) K) with hY₁def
  set Y₂ := (y₂ : Matrix (Fin 3) (Fin 3) K) with hY₂def
  have hY₁u : (Y₁.map h.bar)ᵀ * Y₁ = 1 := (mem_glPi_false h).mp hH₁
  have hY₂u : (Y₂.map h.bar)ᵀ * Y₂ = 1 := (mem_glPi_false h).mp hH₂
  have hY₁u' : Y₁ * (Y₁.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hY₁u
  obtain ⟨P₀, hP₀⟩ := exists_conj_gl hℓ h₁ h₂
  set Pm := (P₀ : Matrix (Fin 3) (Fin 3) K) with hPmdef
  set Pc := (Pm.map h.bar)ᵀ with hPcdef
  have hct : (Y₁.map h.bar)ᵀ * Pc = Pc * (Y₂.map h.bar)ᵀ := by
    have := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => (A.map h.bar)ᵀ) hP₀
    simp only [ct_mul] at this
    exact this
  have h1 : Pc * Y₂ = Y₁ * Pc := by
    calc Pc * Y₂ = Y₁ * (Y₁.map h.bar)ᵀ * Pc * Y₂ := by rw [hY₁u', Matrix.one_mul]
      _ = Y₁ * ((Y₁.map h.bar)ᵀ * Pc) * Y₂ := by simp only [Matrix.mul_assoc]
      _ = Y₁ * (Pc * (Y₂.map h.bar)ᵀ) * Y₂ := by rw [hct]
      _ = Y₁ * Pc * ((Y₂.map h.bar)ᵀ * Y₂) := by simp only [Matrix.mul_assoc]
      _ = Y₁ * Pc := by rw [hY₂u, Matrix.mul_one]
  set M := Pc * Pm with hMdef
  have hMy : M * Y₁ = Y₁ * M := by
    calc M * Y₁ = Pc * (Pm * Y₁) := Matrix.mul_assoc _ _ _
      _ = Pc * (Y₂ * Pm) := by rw [hP₀]
      _ = (Pc * Y₂) * Pm := (Matrix.mul_assoc _ _ _).symm
      _ = (Y₁ * Pc) * Pm := by rw [h1]
      _ = Y₁ * M := Matrix.mul_assoc _ _ _
  have hMh : (M.map h.bar)ᵀ = M := by rw [hMdef, ct_mul, hPcdef, ct_ct]
  obtain ⟨m, hm⟩ := (mem_range_cubeHom hℓ h₁ M).mpr hMy
  have hmfix : h3.bar m = m := by
    apply cubeHom_injective hℓ h₁
    rw [key, hm, hMh]
  have hPdet : Pm.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P₀.isUnit).ne_zero
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hm
    have := congrArg Matrix.det hm
    rw [det_zero, hMdef, det_mul, hPcdef, det_transpose,
      show (Pm.map h.bar).det = h.bar Pm.det from (RingHom.map_det h.bar _).symm] at this
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hPdet) hPdet this.symm
  obtain ⟨δ, hδ⟩ := h3.normHom_surjective ⟨m⁻¹, h3.mem_fixedField.mpr (by rw [map_inv₀, hmfix])⟩
  have hδm : δ * h3.bar δ * m = 1 := by
    have := congrArg Subtype.val hδ
    simp only [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
    rw [this, inv_mul_cancel₀ hm0]
  set D := cubeHom h₁ δ with hDdef
  set P₁ := Pm * D with hP₁def
  have hP₁u : (P₁.map h.bar)ᵀ * P₁ = 1 := by
    rw [hP₁def, ct_mul, hDdef, ← key]
    calc cubeHom h₁ (h3.bar δ) * Pc * (Pm * cubeHom h₁ δ) =
        cubeHom h₁ (h3.bar δ) * M * cubeHom h₁ δ := by simp only [hMdef, Matrix.mul_assoc]
      _ = cubeHom h₁ (h3.bar δ * m * δ) := by rw [map_mul, map_mul, hm]
      _ = 1 := by rw [show h3.bar δ * m * δ = δ * h3.bar δ * m by ring, hδm, map_one]
  have hP₁y : P₁ * Y₁ = Y₂ * P₁ := by
    have hDY : D * Y₁ = Y₁ * D := (mem_range_cubeHom hℓ h₁ D).mp ⟨δ, rfl⟩
    calc P₁ * Y₁ = Pm * (D * Y₁) := Matrix.mul_assoc _ _ _
      _ = Pm * Y₁ * D := by rw [hDY, Matrix.mul_assoc]
      _ = Y₂ * Pm * D := by rw [hP₀]
      _ = Y₂ * P₁ := by rw [hP₁def, Matrix.mul_assoc]
  have hP₁unit : IsUnit P₁ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hP₁u)
  refine ⟨hP₁unit.unit, ?_, ?_⟩
  · rw [mem_glPi_false h]
    exact hP₁u
  · exact hP₁y

end Unitary

section SL

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_conj_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y₁ y₂ : GL (Fin 3) K} (hH₁ : y₁ ∈ glPi π 3 (p ^ f) K) (hH₂ : y₂ ∈ glPi π 3 (p ^ f) K)
    {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (h₁ : (y₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1)
    (h₂ : (y₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ t ∈ slPi π 3 (p ^ f) K, t * y₁ * t⁻¹ = y₂ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨P, hPH, hP⟩ : ∃ P : GL (Fin 3) K, P ∈ glPi π 3 (p ^ f) K ∧
      (P : Matrix (Fin 3) (Fin 3) K) * y₁ = y₂ * P := by
    cases π
    · exact exists_conj_gu hK hq hH₁ hH₂ hℓ h₁ h₂
    · obtain ⟨P, hP⟩ := exists_conj_gl hℓ h₁ h₂
      exact ⟨P, mem_glPi_true _ P, hP⟩
  obtain ⟨c, hc⟩ : (⟨GeneralLinearGroup.det P, det_mem_rootsOfUnity hK hPH⟩ :
      rootsOfUnity (qSubPi π (p ^ f)) K)⁻¹ ∈ (detCent hK y₁).range := by
    rw [range_detCent hK hq hH₁ hℓ h₁]
    exact Subgroup.mem_top _
  obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp c.2
  have hcy : (c : GL (Fin 3) K) * y₁ = y₁ * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hcdet : GeneralLinearGroup.det (c : GL (Fin 3) K) = (GeneralLinearGroup.det P)⁻¹ := by
    have := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => (t : Kˣ)) hc
    simpa [detCent] using this
  have hPy : P * y₁ = y₂ * P := Units.ext hP
  generalize (c : GL (Fin 3) K) = cc at hcH hcy hcdet
  refine ⟨P * cc, ?_, ?_⟩
  · rw [mem_slPi_iff hπ]
    refine ⟨mul_mem hPH hcH, det_eq_one_of_units ?_⟩
    rw [map_mul, hcdet, mul_inv_cancel]
  · calc P * cc * y₁ * (P * cc)⁻¹ = P * (cc * y₁) * cc⁻¹ * P⁻¹ := by group
      _ = P * (y₁ * cc) * cc⁻¹ * P⁻¹ := by rw [hcy]
      _ = P * y₁ * P⁻¹ := by group
      _ = y₂ := by rw [hPy]; group

end SL

end A318P

end CFSG.Quasithin
