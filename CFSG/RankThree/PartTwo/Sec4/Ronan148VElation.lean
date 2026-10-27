module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148VHomology
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.Classical.SemilinearFixedBasis

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem exists_eq_smul_one_of_mem_scalars {S : SpecialLinearGroup (Fin 3) F}
    (hS : S ∈ scalars 3 F) : ∃ c : F, c ≠ 0 ∧ (S : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hS
  exact ⟨c, c.ne_zero, by rw [hc, scalar_apply, smul_one_eq_diagonal]⟩

theorem exists_smul_of_proj_eq {A B : SpecialLinearGroup (Fin 3) F}
    (h : proj 3 F A = proj 3 F B) :
    ∃ c : F, c ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) F) = c • (A : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨c, hc0, hc⟩ := exists_eq_smul_one_of_mem_scalars (proj_eq_proj_iff.mp h)
  refine ⟨c, hc0, ?_⟩
  have e : (B : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ * B : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [e, hc, mul_smul_comm, mul_one]

theorem proj_eq_one_of_eq_smul_one {A : SpecialLinearGroup (Fin 3) F} {a : F}
    (h : (A : Matrix (Fin 3) (Fin 3) F) = a • 1) : proj 3 F A = 1 := by
  rw [proj_eq_one_iff]
  have hdet : a ^ 3 = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe A
    rw [h, det_smul, det_one, Fintype.card_fin, mul_one] at h1
    exact h1
  have ha : a ≠ 0 := by
    rintro rfl
    norm_num at hdet
  refine mem_scalars.mpr ⟨Units.mk0 a ha, Units.ext ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]
  · rw [h, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]

theorem eq_zero_of_one_add_vecMulVec_eq_smul_one {v y : Fin 3 → F} {c : F} (hv : v ≠ 0)
    (h : 1 + vecMulVec v y = c • (1 : Matrix (Fin 3) (Fin 3) F)) : y = 0 := by
  have h1 : (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec v y =
      c • 1 + vecMulVec v (0 : Fin 3 → F) := by
    rw [one_smul, h]
    ext i j
    simp [vecMulVec_apply]
  obtain ⟨-, h2⟩ := eq_of_smul_one_add_vecMulVec_eq h1
  have h3 : vecMulVec v y = 0 := by
    rw [h2]
    ext i j
    simp [vecMulVec_apply]
  exact (vecMulVec_eq_zero.mp h3).resolve_left hv

theorem eq_of_vecMulVec_eq {v y y' : Fin 3 → F} (hv : v ≠ 0)
    (h : vecMulVec v y = vecMulVec v y') : y = y' := by
  have h1 : vecMulVec v (y - y') = 0 := by rw [vecMulVec_sub, h, sub_self]
  exact sub_eq_zero.mp ((vecMulVec_eq_zero.mp h1).resolve_left hv)

@[expose] def elation (v y : Fin 3 → F) (hy : y ⬝ᵥ v = 0) : SpecialLinearGroup (Fin 3) F :=
  ⟨1 + vecMulVec v y, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hy, add_zero]⟩

@[simp]
theorem coe_elation (v y : Fin 3 → F) (hy : y ⬝ᵥ v = 0) :
    (elation v y hy : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec v y :=
  rfl

theorem one_add_vecMulVec_mul {v y y' : Fin 3 → F} (hy : y ⬝ᵥ v = 0) :
    (1 + vecMulVec v y) * (1 + vecMulVec v y') = 1 + vecMulVec v (y + y') := by
  rw [add_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, hy, zero_smul, vecMulVec_add]
  have h0 : vecMulVec v (0 : Fin 3 → F) = 0 := by
    ext i j
    simp [vecMulVec_apply]
  rw [h0, add_zero]
  abel

section CharTwo

variable [CharP F 2]

@[expose] def elationLine (v : Fin 3 → F) : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | ∃ y : Fin 3 → F, y ⬝ᵥ v = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec v y}
  mul_mem' := by
    rintro a b ⟨y, hy, ha⟩ ⟨y', hy', hb⟩
    refine ⟨y + y', by rw [add_dotProduct, hy, hy', add_zero], ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ha, hb, one_add_vecMulVec_mul hy]
  one_mem' := ⟨0, zero_dotProduct v, by
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    simp [vecMulVec_apply]⟩
  inv_mem' := by
    rintro a ⟨y, hy, ha⟩
    have haa : a * a = 1 := by
      apply Subtype.ext
      have hyy : y + y = 0 := funext fun i => CharTwo.add_self_eq_zero (y i)
      rw [Matrix.SpecialLinearGroup.coe_mul, ha, one_add_vecMulVec_mul hy, hyy,
        Matrix.SpecialLinearGroup.coe_one]
      ext i j
      simp [vecMulVec_apply]
    rw [inv_eq_of_mul_eq_one_right haa]
    exact ⟨y, hy, ha⟩

theorem elation_mem_elationLine (v y : Fin 3 → F) (hy : y ⬝ᵥ v = 0) :
    elation v y hy ∈ elationLine v :=
  ⟨y, hy, rfl⟩

theorem mul_self_of_mem_elationLine {v : Fin 3 → F} {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ elationLine v) : g * g = 1 := by
  obtain ⟨y, hy, ha⟩ := hg
  apply Subtype.ext
  have hyy : y + y = 0 := funext fun i => CharTwo.add_self_eq_zero (y i)
  rw [Matrix.SpecialLinearGroup.coe_mul, ha, one_add_vecMulVec_mul hy, hyy,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  simp [vecMulVec_apply]

theorem conj_mem_elationLine {v : Fin 3 → F} {G : SpecialLinearGroup (Fin 3) F} {a : F}
    (hGv : (G : Matrix (Fin 3) (Fin 3) F) *ᵥ v = a • v) {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ elationLine v) : G * g * G⁻¹ ∈ elationLine v := by
  obtain ⟨y, hy, hgy⟩ := hg
  set Gi := ((G⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGGi : (G : Matrix (Fin 3) (Fin 3) F) * Gi = 1 := by
    rw [hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hGiG : Gi * (G : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hGi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hGiv : a • (Gi *ᵥ v) = v := by
    rw [← mulVec_smul, ← hGv, mulVec_mulVec, hGiG, one_mulVec]
  refine ⟨a • (y ᵥ* Gi), ?_, ?_⟩
  · rw [smul_dotProduct, ← dotProduct_mulVec, ← dotProduct_smul, hGiv, hy]
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgy, mul_add,
      mul_one, add_mul, hGGi, mul_vecMulVec, vecMulVec_mul, hGv, smul_vecMulVec, vecMulVec_smul]

theorem map_mem_elationLine {v : Fin 3 → F} {ρ : F ≃+* F} {a : F}
    (hρv : ∀ i, ρ (v i) = a * v i) {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ elationLine v) : Matrix.SpecialLinearGroup.map ρ.toRingHom g ∈ elationLine v := by
  obtain ⟨y, hy, hgy⟩ := hg
  refine ⟨a • fun i => ρ (y i), ?_, ?_⟩
  · have h1 : ρ (y ⬝ᵥ v) = a * ((fun i => ρ (y i)) ⬝ᵥ v) := by
      simp only [dotProduct, map_sum, map_mul, hρv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [smul_dotProduct, smul_eq_mul, ← h1, hy, map_zero]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hgy]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [vecMulVec_apply, hρv]
      ring
    · simp [vecMulVec_apply, hρv, Matrix.one_apply_ne hij]
      ring

end CharTwo

theorem apply_apply_apply_of_orderOf_eq_three {τ : F ≃+* F} (hτ : orderOf τ = 3) (x : F) :
    τ (τ (τ x)) = x := by
  have h := pow_orderOf_eq_one τ
  rw [hτ] at h
  have h1 := congrArg (fun f : F ≃+* F => f x) h
  simpa [pow_succ] using h1

theorem norm_eq_one_of_map_eq_smul {τ : F ≃+* F} (hτ : orderOf τ = 3) {v : Fin 3 → F}
    (hv : v ≠ 0) {a : F} (hτv : ∀ i, τ (v i) = a * v i) : a * τ a * τ (τ a) = 1 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have h1 := apply_apply_apply_of_orderOf_eq_three hτ (v i₀)
  rw [hτv, map_mul, hτv, map_mul, map_mul, hτv] at h1
  apply mul_right_cancel₀ hi₀
  linear_combination h1

theorem exists_fixed_perp {τ : F ≃+* F} (hτ : orderOf τ = 3) {v : Fin 3 → F} (hv : v ≠ 0)
    {a b : F} (hτv : ∀ i, τ (v i) = a * v i) (hb : b * τ b * τ (τ b) = 1) :
    ∃ y : Fin 3 → F, y ≠ 0 ∧ y ⬝ᵥ v = 0 ∧ ∀ i, b * τ (y i) = y i := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hb
    exact zero_ne_one hb
  have hτ3 := apply_apply_apply_of_orderOf_eq_three hτ
  let M : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun y i => b * τ (y i)
      invFun := fun y i => τ.symm (b⁻¹ * y i)
      left_inv := fun y => by
        funext i
        simp [hb0]
      right_inv := fun y => by
        funext i
        simp [hb0]
      map_add' := fun y y' => by
        funext i
        simp [mul_add] }
  have hMapp : ∀ y i, M y i = b * τ (y i) := fun _ _ => rfl
  have hM : ∀ (c : F) (y : Fin 3 → F), M (c • y) = τ c • M y := by
    intro c y
    funext i
    rw [hMapp, Pi.smul_apply, Pi.smul_apply, hMapp, smul_eq_mul, smul_eq_mul, map_mul]
    ring
  have hM3 : ∀ y, (⇑M)^[3] y = y := by
    intro y
    funext i
    change M (M (M y)) i = y i
    rw [hMapp, hMapp, hMapp]
    simp only [map_mul, hτ3]
    linear_combination (y i) * hb
  have hspan := CFSG.RankThree.Classical.span_fixed_eq_top τ (by norm_num) hτ M hM hM3
  have hfix : ∀ y ∈ CFSG.RankThree.Classical.fixedSet M, ∀ i, b * τ (y i) = y i :=
    fun y hy i => congrFun hy i
  obtain ⟨y₁, hy₁, hy₁v⟩ : ∃ y ∈ CFSG.RankThree.Classical.fixedSet M, y ⬝ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let L : (Fin 3 → F) →ₗ[F] F :=
      { toFun := fun y => y ⬝ᵥ v
        map_add' := fun y y' => add_dotProduct y y' v
        map_smul' := fun c y => smul_dotProduct c y v }
    have hle : Submodule.span F (CFSG.RankThree.Classical.fixedSet M) ≤ LinearMap.ker L :=
      Submodule.span_le.mpr fun y hy => hcon y hy
    rw [hspan] at hle
    apply hi₀
    have h1 : (Pi.single i₀ 1 : Fin 3 → F) ∈ LinearMap.ker L := hle Submodule.mem_top
    rw [LinearMap.mem_ker] at h1
    change (Pi.single i₀ 1 : Fin 3 → F) ⬝ᵥ v = 0 at h1
    rwa [single_dotProduct, one_mul] at h1
  obtain ⟨y₂, hy₂, hy₂s⟩ : ∃ y ∈ CFSG.RankThree.Classical.fixedSet M,
      y ∉ Submodule.span F {y₁} := by
    by_contra hcon
    push Not at hcon
    have hy₁0 : y₁ ≠ 0 := by
      rintro rfl
      exact hy₁v (zero_dotProduct v)
    have hle : Submodule.span F (CFSG.RankThree.Classical.fixedSet M) ≤
        Submodule.span F {y₁} := Submodule.span_le.mpr hcon
    rw [hspan] at hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun, finrank_span_singleton hy₁0] at h1
    omega
  have hc : ∀ y ∈ CFSG.RankThree.Classical.fixedSet M, b * τ (y ⬝ᵥ v) = a * (y ⬝ᵥ v) := by
    intro y hy
    simp only [dotProduct, map_sum, map_mul, hτv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (a * v i) * hfix y hy i
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = y₁ ⬝ᵥ v := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = y₂ ⬝ᵥ v := ⟨_, rfl⟩
  rw [← hc₁] at hy₁v
  have e1 := hc y₁ hy₁
  have e2 := hc y₂ hy₂
  rw [← hc₁] at e1
  rw [← hc₂] at e2
  have hτc₁ : τ c₁ ≠ 0 := fun h0 => hy₁v ((map_eq_zero_iff τ τ.injective).mp h0)
  have hq : τ (c₂ / c₁) = c₂ / c₁ := by
    rw [map_div₀, div_eq_div_iff hτc₁ hy₁v]
    have h1 : b * (τ c₂ * c₁ - c₂ * τ c₁) = 0 := by linear_combination c₁ * e2 - c₂ * e1
    linear_combination (mul_eq_zero.mp h1).resolve_left hb0
  refine ⟨y₂ - (c₂ / c₁) • y₁, ?_, ?_, ?_⟩
  · intro h0
    apply hy₂s
    rw [sub_eq_zero] at h0
    rw [h0]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y₁)
  · rw [sub_dotProduct, smul_dotProduct, ← hc₁, ← hc₂, smul_eq_mul, div_mul_cancel₀ _ hy₁v,
      sub_self]
  · intro i
    have f1 := hfix y₁ hy₁ i
    have f2 := hfix y₂ hy₂ i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hq]
    linear_combination f2 - (c₂ / c₁) * f1

theorem homology_mul_elation {κ : F} {v φ y : Fin 3 → F} (hκ : κ ≠ 0) (hy : y ⬝ᵥ v = 0) :
    (κ • (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec v φ) * (1 + vecMulVec v y) =
      (1 + vecMulVec v (((κ + φ ⬝ᵥ v) / κ) • y)) * (κ • 1 + vecMulVec v φ) := by
  have he : (κ + φ ⬝ᵥ v) / κ * κ = κ + φ ⬝ᵥ v := div_mul_cancel₀ _ hκ
  have hPN : vecMulVec v y * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hy, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  have hNP : vecMulVec v φ * vecMulVec v y = (φ ⬝ᵥ v) • vecMulVec v y := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  rw [vecMulVec_smul, mul_add, mul_one, add_mul, smul_mul_assoc, one_mul, hNP, add_mul, one_mul,
    mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_one, hPN, smul_zero, add_zero,
    smul_smul, he, add_smul]

theorem exists_eigen_of_proj_commute {Z G : SpecialLinearGroup (Fin 3) F} {κ : F}
    {v φ : Fin 3 → F} (hφ : φ ≠ 0) (hZ : (Z : Matrix (Fin 3) (Fin 3) F) = κ • 1 + vecMulVec v φ)
    (h : proj 3 F G * proj 3 F Z = proj 3 F Z * proj 3 F G) :
    ∃ a : F, (G : Matrix (Fin 3) (Fin 3) F) *ᵥ v = a • v := by
  obtain ⟨μ, -, hμ⟩ := exists_smul_of_proj_eq (A := Z) (B := G * Z * G⁻¹) (by
    rw [map_mul, map_mul, h, map_inv, mul_inv_cancel_right])
  set Gi := ((G⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGGi : (G : Matrix (Fin 3) (Fin 3) F) * Gi = 1 := by
    rw [hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hGiG : Gi * (G : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hGi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hZ] at hμ
  have e : (G : Matrix (Fin 3) (Fin 3) F) * (κ • 1 + vecMulVec v φ) * Gi =
      κ • 1 + vecMulVec ((G : Matrix (Fin 3) (Fin 3) F) *ᵥ v) (φ ᵥ* Gi) := by
    rw [mul_add, add_mul, mul_smul_comm, mul_one, smul_mul_assoc, hGGi, mul_vecMulVec,
      vecMulVec_mul]
  rw [e, smul_add, smul_smul, ← smul_vecMulVec] at hμ
  obtain ⟨-, h2⟩ := eq_of_smul_one_add_vecMulVec_eq hμ
  have hφ' : φ ᵥ* Gi ≠ 0 := by
    intro h0
    apply hφ
    have h1 := congrArg (fun x => x ᵥ* (G : Matrix (Fin 3) (Fin 3) F)) h0
    simp only [vecMul_vecMul, hGiG, vecMul_one, zero_vecMul] at h1
    exact h1
  obtain ⟨c, hc⟩ := exists_smul_eq_of_vecMulVec_eq hφ' h2
  exact ⟨c * μ, by rw [hc, smul_smul]⟩

theorem fieldAut_homology_data {Z : SpecialLinearGroup (Fin 3) F} {κ : F} {v φ : Fin 3 → F}
    (hκ : κ ≠ 0) (hφ : φ ≠ 0) (hZ : (Z : Matrix (Fin 3) (Fin 3) F) = κ • 1 + vecMulVec v φ)
    {ρ : F ≃+* F} (h : fieldAut 3 F ρ (proj 3 F Z) = proj 3 F Z) :
    (∃ a : F, ∀ i, ρ (v i) = a * v i) ∧ ρ ((κ + φ ⬝ᵥ v) / κ) = (κ + φ ⬝ᵥ v) / κ := by
  rw [fieldAut_proj] at h
  obtain ⟨μ, hμ0, hμ⟩ := exists_smul_of_proj_eq h.symm
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hZ] at hμ
  have e : (κ • (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec v φ).map ρ.toRingHom =
      ρ κ • 1 + vecMulVec (fun i => ρ (v i)) (fun i => ρ (φ i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [vecMulVec_apply]
    · simp [vecMulVec_apply, Matrix.one_apply_ne hij]
  rw [e, smul_add, smul_smul, ← smul_vecMulVec] at hμ
  obtain ⟨h1, h2⟩ := eq_of_smul_one_add_vecMulVec_eq hμ
  have hφ' : (fun i => ρ (φ i)) ≠ 0 := by
    intro h0
    apply hφ
    funext i
    have h1 := congrFun h0 i
    simpa using h1
  obtain ⟨c, hc⟩ := exists_smul_eq_of_vecMulVec_eq hφ' h2
  refine ⟨⟨c * μ, fun i => ?_⟩, ?_⟩
  · have h1 := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    ring
  · have h3 : ρ (φ ⬝ᵥ v) = μ * (φ ⬝ᵥ v) := by
      simp only [dotProduct, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 := congrFun (congrFun h2 i) i
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul] at h4
      linear_combination h4
    rw [map_div₀, map_add, h1, h3, div_eq_div_iff (mul_ne_zero hμ0 hκ) hκ]
    ring

theorem homology_ratio_pow_three {Z : Matrix (Fin 3) (Fin 3) F} {κ c : F} {v φ : Fin 3 → F}
    (hκ : κ ≠ 0) (hv : v ≠ 0) (hZ : Z = κ • 1 + vecMulVec v φ) (hZ3 : Z ^ 3 = c • 1) :
    ((κ + φ ⬝ᵥ v) / κ) ^ 3 = 1 := by
  have hZv : Z *ᵥ v = (κ + φ ⬝ᵥ v) • v := by
    rw [hZ, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, add_smul]
  obtain ⟨x, hx0, hx, -⟩ := exists_ne_zero_dotProduct_eq_zero φ φ
  have hZx : Z *ᵥ x = κ • x := by
    rw [hZ, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hx, MulOpposite.op_zero,
      zero_smul, add_zero]
  have hcube : ∀ (w : Fin 3 → F) (r : F), w ≠ 0 → Z *ᵥ w = r • w → r ^ 3 = c := by
    intro w r hw hZw
    have h1 : (Z ^ 3) *ᵥ w = r ^ 3 • w := by
      simp only [pow_three', ← mulVec_mulVec, hZw, mulVec_smul, smul_smul]
      congr 1
      ring
    rw [hZ3, smul_mulVec, one_mulVec] at h1
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw (funext hcon)
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hi h2).symm
  have h1 := hcube v _ hv hZv
  have h2 := hcube x κ hx0 hZx
  have hκ3 : κ ^ 3 ≠ 0 := pow_ne_zero 3 hκ
  rw [div_pow, h1, ← h2, div_self hκ3]

section Finite

variable [Finite F] [CharP F 2]

theorem exists_homology_lift {z t : projectiveSL 3 F} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hzt : z * t = t * z) :
    ∃ Z : SpecialLinearGroup (Fin 3) F, proj 3 F Z = z ∧ ∃ (κ : F) (v φ : Fin 3 → F),
      κ ≠ 0 ∧ v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v ≠ 0 ∧
        (Z : Matrix (Fin 3) (Fin 3) F) = κ • 1 + vecMulVec v φ := by
  obtain ⟨Z, rfl⟩ := proj_surjective 3 F z
  obtain ⟨T, rfl⟩ := proj_surjective 3 F t
  refine ⟨Z, rfl, ?_⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨c, hc0, hc⟩ := exists_eq_smul_one_of_mem_scalars
    (proj_eq_one_iff.mp (by rw [map_pow]; exact hz3) : Z ^ 3 ∈ scalars 3 F)
  rw [Matrix.SpecialLinearGroup.coe_pow] at hc
  have hZs : ∀ a : F, (Z : Matrix (Fin 3) (Fin 3) F) ≠ a • 1 := fun a ha =>
    hz1 (proj_eq_one_of_eq_smul_one ha)
  obtain ⟨d, hd0, hd⟩ := exists_eq_smul_one_of_mem_scalars
    (proj_eq_one_iff.mp (by rw [map_pow]; exact ht2) : T ^ 2 ∈ scalars 3 F)
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two] at hd
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' d
  have hTs : (T : Matrix (Fin 3) (Fin 3) F) ≠ s • 1 := fun ha =>
    ht1 (proj_eq_one_of_eq_smul_one ha)
  obtain ⟨μ, -, hμ⟩ := exists_smul_of_proj_eq (A := Z * T) (B := T * Z) (by
    rw [map_mul, map_mul]; exact hzt)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hμ
  have hμ1 : μ = 1 := by
    have e1 : (T : Matrix (Fin 3) (Fin 3) F) * T * Z =
        μ ^ 2 • ((Z : Matrix (Fin 3) (Fin 3) F) * (T * T)) := by
      calc (T : Matrix (Fin 3) (Fin 3) F) * T * Z = T * (T * Z) := by rw [mul_assoc]
        _ = T * (μ • (Z * T)) := by rw [hμ]
        _ = μ • ((T * Z) * T) := by rw [mul_smul_comm, mul_assoc]
        _ = μ • ((μ • (Z * T)) * T) := by rw [hμ]
        _ = μ ^ 2 • (Z * (T * T)) := by rw [smul_mul_assoc, smul_smul, mul_assoc, sq]
    rw [hd, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul] at e1
    have hZ0 : (Z : Matrix (Fin 3) (Fin 3) F) ≠ 0 := fun h0 => hZs 0 (by rw [h0, zero_smul])
    have e2 : (d - μ ^ 2 * d) • (Z : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [sub_smul, e1, sub_self]
    have e3 : d - μ ^ 2 * d = 0 := (smul_eq_zero.mp e2).resolve_right hZ0
    have e4 : μ ^ 2 = 1 := mul_right_cancel₀ hd0 (by linear_combination -e3)
    have e5 : (μ + 1) ^ 2 = 0 := by linear_combination e4 + (μ + 1) * h2
    have e6 : μ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e5
    linear_combination e6 - h2
  rw [hμ1, one_smul] at hμ
  exact exists_homology_of_commute hc0 hc hZs hμ.symm (by rw [hd, hs, sq]) hTs

theorem coe_conj_homology {Z g : SpecialLinearGroup (Fin 3) F} {κ : F} {v φ y : Fin 3 → F}
    (hκ : κ ≠ 0) (hZ : (Z : Matrix (Fin 3) (Fin 3) F) = κ • 1 + vecMulVec v φ)
    (hy : y ⬝ᵥ v = 0) (hg : (g : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec v y) :
    ((Z * g * Z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec v (((κ + φ ⬝ᵥ v) / κ) • y) := by
  have hZZi : (Z : Matrix (Fin 3) (Fin 3) F) *
      ((Z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hZ,
    homology_mul_elation hκ hy, ← hZ, mul_assoc, hZZi, mul_one]

theorem eq_one_of_commutator_commute {Z g : SpecialLinearGroup (Fin 3) F} {κ : F}
    {v φ : Fin 3 → F} (hκ : κ ≠ 0) (hv : v ≠ 0) (hφv : φ ⬝ᵥ v ≠ 0)
    (hZ : (Z : Matrix (Fin 3) (Fin 3) F) = κ • 1 + vecMulVec v φ) (hg : g ∈ elationLine v)
    (h : ⁅proj 3 F g, proj 3 F Z⁆ * proj 3 F Z = proj 3 F Z * ⁅proj 3 F g, proj 3 F Z⁆) :
    proj 3 F g = 1 := by
  obtain ⟨y, hy, hgy⟩ := hg
  obtain ⟨e, he⟩ : ∃ e : F, e = (κ + φ ⬝ᵥ v) / κ := ⟨_, rfl⟩
  have he1 : e + 1 ≠ 0 := by
    intro h0
    apply hφv
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h3 : (κ + φ ⬝ᵥ v) / κ * κ = κ + φ ⬝ᵥ v := div_mul_cancel₀ _ hκ
    rw [← he] at h3
    linear_combination -h3 + κ * h0 - κ * h2
  have hh := coe_conj_homology hκ hZ hy hgy
  rw [← he] at hh
  have hgg : g * g = 1 := mul_self_of_mem_elationLine ⟨y, hy, hgy⟩
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hcomm : ⁅g, Z⁆ = g * (Z * g * Z⁻¹) := by
    rw [commutatorElement_def, hginv]
    group
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, w = y + e • y := ⟨_, rfl⟩
  have hwv : w ⬝ᵥ v = 0 := by
    rw [hw, add_dotProduct, smul_dotProduct, hy, smul_zero, add_zero]
  have hc : ((⁅g, Z⁆ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec v w := by
    rw [hcomm, Matrix.SpecialLinearGroup.coe_mul, hgy, hh, one_add_vecMulVec_mul hy, ← hw]
  have hc' := coe_conj_homology hκ hZ hwv hc
  rw [← he] at hc'
  have hpc : proj 3 F ⁅g, Z⁆ = proj 3 F (Z * ⁅g, Z⁆ * Z⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_commutatorElement, ← h, mul_inv_cancel_right]
  obtain ⟨μ, -, hμ⟩ := exists_smul_of_proj_eq hpc
  rw [hc', hc] at hμ
  have hμ' : (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) + vecMulVec v (e • w) =
      μ • 1 + vecMulVec v (μ • w) := by
    rw [one_smul, hμ, vecMulVec_smul, smul_add]
  obtain ⟨hμ1, h2⟩ := eq_of_smul_one_add_vecMulVec_eq hμ'
  rw [← hμ1, one_smul] at h2
  have h3 := eq_of_vecMulVec_eq hv h2
  have h4 : ((e + 1) * (e + 1)) • y = 0 := by
    have h2' : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h5 : (e • w - w) = ((e + 1) * (e + 1)) • y := by
      rw [hw, smul_add, smul_smul]
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(y i) - e * y i) * h2'
    rw [← h5, h3, sub_self]
  have hy0 : y = 0 := (smul_eq_zero.mp h4).resolve_left (mul_ne_zero he1 he1)
  apply proj_eq_one_of_eq_smul_one (a := 1)
  rw [hgy, hy0, one_smul]
  ext i j
  simp [vecMulVec_apply]

theorem exists_elation_model {τ : F ≃+* F} (hτ : orderOf τ = 3) {z t : projectiveSL 3 F}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hzt : z * t = t * z)
    (hτz : fieldAut 3 F τ z = z) :
    ∃ U : Subgroup (projectiveSL 3 F), (∀ u ∈ U, u * u = 1) ∧
      (∀ g, g * z = z * g → ∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧ (∀ u ∈ U, fieldAut 3 F τ u ∈ U) ∧
      (∃ u ∈ U, fieldAut 3 F τ (z * u * z⁻¹) = u ∧ u ≠ 1) ∧
      ∀ u ∈ U, ⁅u, z⁆ * z = z * ⁅u, z⁆ → u = 1 := by
  obtain ⟨Z, rfl, κ, v, φ, hκ, hv, hφ, hφv, hZ⟩ := exists_homology_lift hz3 hz1 ht2 ht1 hzt
  obtain ⟨⟨a, ha⟩, he⟩ := fieldAut_homology_data hκ hφ hZ hτz
  obtain ⟨c, -, hc⟩ := exists_eq_smul_one_of_mem_scalars
    (proj_eq_one_iff.mp (by rw [map_pow]; exact hz3) : Z ^ 3 ∈ scalars 3 F)
  rw [Matrix.SpecialLinearGroup.coe_pow] at hc
  have he3 := homology_ratio_pow_three hκ hv hZ hc
  obtain ⟨e, he'⟩ : ∃ e : F, e = (κ + φ ⬝ᵥ v) / κ := ⟨_, rfl⟩
  rw [← he'] at he he3
  have hN := norm_eq_one_of_map_eq_smul hτ hv ha
  have hb : (a * e) * τ (a * e) * τ (τ (a * e)) = 1 := by
    rw [map_mul, map_mul, he, he]
    linear_combination (e ^ 3) * hN + he3
  obtain ⟨y, hy0, hyv, hyfix⟩ := exists_fixed_perp hτ hv ha hb
  refine ⟨(elationLine v).map (proj 3 F), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, mul_self_of_mem_elationLine hg, map_one]
  · rintro g hg _ ⟨w, hw, rfl⟩
    obtain ⟨G, rfl⟩ := proj_surjective 3 F g
    obtain ⟨b', hb'⟩ := exists_eigen_of_proj_commute hφ hZ hg
    exact ⟨G * w * G⁻¹, conj_mem_elationLine hb' hw, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, map_mem_elationLine ha hw, (fieldAut_proj τ w).symm⟩
  · refine ⟨proj 3 F (elation v y hyv), ⟨_, elation_mem_elationLine v y hyv, rfl⟩, ?_, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul, fieldAut_proj]
      congr 1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        coe_conj_homology hκ hZ hyv rfl, ← he', coe_elation]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply_eq, vecMulVec_apply,
          Pi.smul_apply, smul_eq_mul, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_add,
          map_one, map_mul, ha, he]
        linear_combination (v i) * hyfix i
      · rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply_ne hij,
          vecMulVec_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_zero, map_mul, ha,
          he, zero_add]
        linear_combination (v i) * hyfix j
    · intro h1
      obtain ⟨c', -, hc'⟩ := exists_eq_smul_one_of_mem_scalars (proj_eq_one_iff.mp h1)
      exact hy0 (eq_zero_of_one_add_vecMulVec_eq_smul_one hv hc')
  · rintro _ ⟨w, hw, rfl⟩ hcomm
    exact eq_one_of_commutator_commute hκ hv hφv hZ hw hcomm

end Finite

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
