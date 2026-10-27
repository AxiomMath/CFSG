module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

variable {n : ℕ} {F₀ : Type} [Field F₀]

private lemma coe_diagSU_eq_diagGL
    (x : rootsOfUnity (2 ^ n + 1) F₀ × rootsOfUnity (2 ^ n + 1) F₀) :
    ((diagSU n F₀ x : ↥(StatedSU 3 (2 ^ n) F₀)) : GL (Fin 3) F₀) =
      TauCeti.diagGL ![(x.1 : F₀ˣ), (x.2 : F₀ˣ), ((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹] := by
  apply Units.ext
  rw [coe_diagSU, TauCeti.diagGL_coe]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma permGL_eq_permutationGL {K : Type} [Field K] (σ : Equiv.Perm (Fin 3)) :
    CFSG.RankThree.Classical.permGL σ = TauCeti.permutationGL (k := K) σ := by
  apply Units.ext
  rw [TauCeti.permutationGL_coe, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]

private lemma permGL_mul_diagGL_mul_inv {K : Type} [Field K]
    (σ : Equiv.Perm (Fin 3)) (t : Fin 3 → Kˣ) :
    CFSG.RankThree.Classical.permGL σ * TauCeti.diagGL t *
        (CFSG.RankThree.Classical.permGL σ)⁻¹ =
      TauCeti.diagGL (fun i => t (σ⁻¹ i)) := by
  simp only [permGL_eq_permutationGL]
  exact TauCeti.permutationGL_mul_diagGL_mul_inv σ t

private lemma finRotate_three_zero : finRotate 3 (0 : Fin 3) = 1 :=
  finRotate_apply_zero

private lemma finRotate_three_one : finRotate 3 (1 : Fin 3) = 2 :=
  finRotate_of_lt (n := 2) (k := 1) (by norm_num)

private lemma finRotate_three_two : finRotate 3 (2 : Fin 3) = 0 :=
  finRotate_last

private lemma finRotate_three_symm_zero : (finRotate 3)⁻¹ (0 : Fin 3) = 2 := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact finRotate_three_two.symm

private lemma finRotate_three_symm_one : (finRotate 3)⁻¹ (1 : Fin 3) = 0 := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact finRotate_three_zero.symm

private lemma finRotate_three_symm_two : (finRotate 3)⁻¹ (2 : Fin 3) = 1 := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact finRotate_three_one.symm

theorem diagSU_mem_statedScalars_iff
    (x : rootsOfUnity (2 ^ n + 1) F₀ × rootsOfUnity (2 ^ n + 1) F₀) :
    ((diagSU n F₀ x : ↥(StatedSU 3 (2 ^ n) F₀)) : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀ ↔
      x.1 = x.2 ∧ x.1 ^ 3 = 1 := by
  rw [StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    have hu' : Matrix.scalar (Fin 3) (u : F₀) =
        Matrix.diagonal ![((x.1 : F₀ˣ) : F₀), ((x.2 : F₀ˣ) : F₀),
          ((((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹ : F₀ˣ) : F₀)] := by
      have h := congrArg (fun g : GL (Fin 3) F₀ => (g : Matrix (Fin 3) (Fin 3) F₀)) hu
      simpa only [Matrix.GeneralLinearGroup.coe_scalar, coe_diagSU] using h
    have h0 : (u : F₀) = ((x.1 : F₀ˣ) : F₀) := by
      have h := congrFun (congrFun hu' 0) 0
      simpa using h
    have h1 : (u : F₀) = ((x.2 : F₀ˣ) : F₀) := by
      have h := congrFun (congrFun hu' 1) 1
      simpa using h
    have h2 : (u : F₀) = ((((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹ : F₀ˣ) : F₀) := by
      have h := congrFun (congrFun hu' 2) 2
      simpa using h
    have ha : (x.1 : F₀ˣ) = (x.2 : F₀ˣ) := Units.ext (h0.symm.trans h1)
    have hc : (x.1 : F₀ˣ) = ((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹ := Units.ext (h0.symm.trans h2)
    have hcube : (x.1 : F₀ˣ) ^ 3 = 1 := by
      have h3 : (x.1 : F₀ˣ) * ((x.1 : F₀ˣ) * (x.2 : F₀ˣ)) = 1 := by
        nth_rewrite 1 [hc]
        exact inv_mul_cancel _
      rw [← ha] at h3
      simpa [pow_succ, pow_two, mul_assoc] using h3
    exact ⟨Subtype.ext ha, Subtype.ext (by simpa using hcube)⟩
  · rintro ⟨h12, h3⟩
    refine ⟨(x.1 : F₀ˣ), ?_⟩
    have ha : (x.1 : F₀ˣ) = (x.2 : F₀ˣ) :=
      congrArg (fun y : rootsOfUnity (2 ^ n + 1) F₀ => (y : F₀ˣ)) h12
    have hcube : (x.1 : F₀ˣ) ^ 3 = 1 := by
      have h := congrArg (fun y : rootsOfUnity (2 ^ n + 1) F₀ => (y : F₀ˣ)) h3
      simpa using h
    have hcinv : ((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹ = (x.1 : F₀ˣ) := by
      rw [← ha, inv_eq_iff_mul_eq_one]
      simpa [pow_succ, pow_two, mul_assoc] using hcube
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagSU, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact congrArg Units.val ha
    · exact (congrArg Units.val hcinv).symm

theorem diagSU_injective : Function.Injective (diagSU n F₀) := by
  intro x y hxy
  have h := congrArg (fun g : ↥(StatedSU 3 (2 ^ n) F₀) => (g : GL (Fin 3) F₀)) hxy
  simp only [coe_diagSU_eq_diagGL] at h
  have ht := TauCeti.diagGL_injective h
  exact Prod.ext (Subtype.ext (by simpa using congrFun ht 0))
    (Subtype.ext (by simpa using congrFun ht 1))

theorem permSU_swap_mul_diagSU_mul_inv [CharP F₀ 2] (a b : rootsOfUnity (2 ^ n + 1) F₀) :
    permSU n F₀ (Equiv.swap 0 1) * diagSU n F₀ (a, b) * (permSU n F₀ (Equiv.swap 0 1))⁻¹ =
      diagSU n F₀ (b, a) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permSU, coe_diagSU_eq_diagGL,
    permGL_mul_diagGL_mul_inv]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def, mul_comm]

theorem permSU_finRotate_mul_diagSU_mul_inv [CharP F₀ 2] (a b : rootsOfUnity (2 ^ n + 1) F₀) :
    permSU n F₀ (finRotate 3) * diagSU n F₀ (a, b) * (permSU n F₀ (finRotate 3))⁻¹ =
      diagSU n F₀ ((a * b)⁻¹, a) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permSU, coe_diagSU_eq_diagGL,
    permGL_mul_diagGL_mul_inv]
  congr 1
  funext i
  fin_cases i
  · simp [finRotate_three_symm_zero]
  · simp [finRotate_three_symm_one]
  · simp [finRotate_three_symm_two]

end CFSG.LocalAnalysis.WeakClosure81

end
