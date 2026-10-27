module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.G11.P4SL34

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def tri (a b c : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [det_fin_three]⟩

theorem coe_tri (a b c : F) :
    ((tri a b c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, c; 0, 1, b; 0, 0, 1] :=
  rfl

theorem tri_mul (a b c a' b' c' : F) :
    tri a b c * tri a' b' c' = tri (a + a') (b + b') (c + c' + a * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem tri_zero : tri (0 : F) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_tri]

theorem tri_inv (a b c : F) : (tri a b c)⁻¹ = tri (-a) (-b) (-c + a * b) := by
  rw [inv_eq_iff_mul_eq_one, tri_mul, ← tri_zero]
  congr 1 <;> ring

theorem tri_mem_unitriangular (a b c : F) : tri a b c ∈ unitriangular 3 F := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_tri] at hij ⊢
  · fin_cases i <;> simp [coe_tri]

theorem exists_tri_of_mem_unitriangular {t : SpecialLinearGroup (Fin 3) F}
    (ht : t ∈ unitriangular 3 F) : ∃ a b c, t = tri a b c := by
  rw [mem_unitriangular] at ht
  obtain ⟨hlow, hdiag⟩ := ht
  refine ⟨(t : Matrix (Fin 3) (Fin 3) F) 0 1, (t : Matrix (Fin 3) (Fin 3) F) 1 2,
    (t : Matrix (Fin 3) (Fin 3) F) 0 2, ?_⟩
  ext i j
  rw [coe_tri]
  fin_cases i <;> fin_cases j <;> simp [hdiag, hlow]

@[expose] noncomputable def graphAut (A : GL (Fin 3) F) (σ : F ≃+* F) :
    MulAut (SpecialLinearGroup (Fin 3) F) :=
  CatalogueBHigherLinearAction.slConjugation 3 F A *
    CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ * CatalogueBGraphForm.slGraphAut 3 F

theorem coe_graphAut (A : GL (Fin 3) F) (σ : F ≃+* F) (x : SpecialLinearGroup (Fin 3) F) :
    ((graphAut A σ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        ((((x⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold graphAut
  rw [MulAut.mul_apply, MulAut.mul_apply, CatalogueBHigherLinearAction.slConjugation_matrix]
  congr 2

@[expose] def IsLowerUni (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ i j : Fin 3, i ≤ j → M i j = (1 : Matrix (Fin 3) (Fin 3) F) i j

theorem core_matrix (A B : Matrix (Fin 3) (Fin 3) F) (hAB : A * B = 1) (hBA : B * A = 1)
    (h1 : IsLowerUni (B * (tri (1 : F) 0 0 : Matrix (Fin 3) (Fin 3) F) * A))
    (h2 : IsLowerUni (B * (tri (0 : F) 1 0 : Matrix (Fin 3) (Fin 3) F) * A))
    (a' b' c' : F) (h : A * !![1, 0, 0; -1, 1, 0; 0, 0, 1] * B =
      (tri a' b' c' : Matrix (Fin 3) (Fin 3) F)) :
    a' = 0 ∧ b' ≠ 0 := by
  have eAB : ∀ i j, A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j =
      (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrFun (congrFun hAB i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have eBA : ∀ i j, B i 0 * A 0 j + B i 1 * A 1 j + B i 2 * A 2 j =
      (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrFun (congrFun hBA i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have s1 : ∀ j, B 0 0 * A 1 j = 0 := by
    intro j
    have := h1 0 j (Fin.zero_le _)
    have e := eBA 0 j
    simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination this - e
  have s2_0 : B 0 0 * A 1 2 = 0 := s1 2
  have s2_1 : B 1 0 * A 1 2 = 0 := by
    have := h1 1 2 (by decide)
    have e := eBA 1 2
    simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] at this e
    linear_combination this - e
  have s2_2 : B 2 0 * A 1 2 = 0 := by
    have := h1 2 2 (by decide)
    have e := eBA 2 2
    simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] at this e
    linear_combination this - e
  have s3 : ∀ j, B 0 1 * A 2 j = 0 := by
    intro j
    have := h2 0 j (Fin.zero_le _)
    have e := eBA 0 j
    simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination this - e
  have t1 : B 0 0 = 0 := by
    have e := eAB 1 1
    simp at e
    linear_combination (-B 0 0) * e + B 0 1 * s1 0 + B 1 1 * s1 1 + B 2 1 * s1 2
  have t2 : B 0 1 = 0 := by
    have e := eAB 2 2
    simp at e
    linear_combination (-B 0 1) * e + B 0 2 * s3 0 + B 1 2 * s3 1 + B 2 2 * s3 2
  have t3 : A 1 2 = 0 := by
    have e := eAB 0 0
    simp at e
    linear_combination (-A 1 2) * e + A 0 0 * s2_0 + A 0 1 * s2_1 + A 0 2 * s2_2
  have t4 : B 0 2 * A 2 0 = 1 := by
    have e := eBA 0 0
    simp at e
    linear_combination e - A 0 0 * t1 - A 1 0 * t2
  have t5 : A 1 1 * B 1 1 = 1 := by
    have e := eAB 1 1
    simp at e
    linear_combination e - A 1 0 * t2 - B 2 1 * t3
  have hB02 : B 0 2 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at t4
    exact zero_ne_one t4
  have hA11 : A 1 1 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at t5
    exact zero_ne_one t5
  have h01 := congrFun (congrFun h 0) 1
  have h12 := congrFun (congrFun h 1) 2
  simp [coe_tri, Matrix.mul_apply, Fin.sum_univ_three] at h01 h12
  have e01 := eAB 0 1
  have e12 := eAB 1 2
  simp at e01 e12
  refine ⟨?_, ?_⟩
  · linear_combination -h01 + e01 - A 0 1 * t2
  · intro hb
    apply mul_ne_zero hA11 hB02
    linear_combination e12 - h12 - hb

theorem isLowerUni_map_transpose (σ : F ≃+* F) {t : SpecialLinearGroup (Fin 3) F}
    (ht : t ∈ unitriangular 3 F) :
    IsLowerUni ((((t : Matrix (Fin 3) (Fin 3) F))ᵀ).map σ) := by
  rw [mem_unitriangular] at ht
  intro i j hij
  rcases hij.lt_or_eq with h | rfl
  · simp [Matrix.transpose_apply, Matrix.map_apply, ht.1 j i h, Matrix.one_apply_ne h.ne]
  · simp [ht.2]

theorem coe_mul_coe_inv (A : GL (Fin 3) F) :
    (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul_coe (A : GL (Fin 3) F) :
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem isLowerUni_conj (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hT : ∀ u ∈ unitriangular 3 F, graphAut A σ u ∈ unitriangular 3 F)
    (hsq : ∀ x, graphAut A σ (graphAut A σ x) = x) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ unitriangular 3 F) :
    IsLowerUni (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
  have ht : graphAut A σ u ∈ unitriangular 3 F := hT u hu
  have h1 := coe_graphAut A σ (graphAut A σ u)
  rw [hsq] at h1
  have h2 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) =
      (((((graphAut A σ u)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).map
        σ) := by
    rw [h1]
    calc _ = (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (A : Matrix (Fin 3) (Fin 3) F)) *
          (((((graphAut A σ u)⁻¹ : SpecialLinearGroup (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F)ᵀ).map σ) *
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (A : Matrix (Fin 3) (Fin 3) F)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [coe_inv_mul_coe, Matrix.one_mul, Matrix.mul_one]
  rw [h2]
  exact isLowerUni_map_transpose σ (inv_mem ht)

theorem sq_ne_one_graphAut [CharP F 2] (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hT : ∀ u ∈ unitriangular 3 F, graphAut A σ u ∈ unitriangular 3 F)
    (hsq : ∀ x, graphAut A σ (graphAut A σ x) = x) :
    ((tri (1 : F) 0 0)⁻¹ * graphAut A σ (tri 1 0 0)) *
      ((tri (1 : F) 0 0)⁻¹ * graphAut A σ (tri 1 0 0)) ≠ 1 := by
  obtain ⟨a', b', c', hβ⟩ :=
    exists_tri_of_mem_unitriangular (hT _ (tri_mem_unitriangular (1 : F) 0 0))
  have h1 := isLowerUni_conj A σ hT hsq (tri_mem_unitriangular (1 : F) 0 0)
  have h2 := isLowerUni_conj A σ hT hsq (tri_mem_unitriangular (0 : F) 1 0)
  have hmat : (A : Matrix (Fin 3) (Fin 3) F) * !![1, 0, 0; -1, 1, 0; 0, 0, 1] *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((tri a' b' c' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hβ, coe_graphAut, tri_inv]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_tri]
  obtain ⟨ha, hb⟩ := core_matrix _ _ (coe_mul_coe_inv A) (coe_inv_mul_coe A) h1 h2 a' b' c' hmat
  rw [hβ, tri_inv, tri_mul, tri_mul]
  intro h
  have h02 := congrArg
    (fun M : SpecialLinearGroup (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp [coe_tri] at h02
  apply hb
  have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
  subst ha
  linear_combination (-1 : F) * h02 + (c' - b') * h2'

theorem commutatorElement_mul_central {G : Type*} [Group G] (a b z₁ z₂ : G)
    (h1 : z₁ ∈ Subgroup.center G) (h2 : z₂ ∈ Subgroup.center G) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c1 : ∀ x : G, ⁅x, z₂⁆ = 1 := fun x => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp h2 x
  have c2 : ∀ x : G, ⁅z₁, x⁆ = 1 := fun x => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp h1 x).symm
  rw [commutatorElement_mul_right_eq_mul_conj, c1, commutatorElement_mul_left_eq_conj_mul, c2]
  simp

theorem descendAut_injective (F : Type) [Field F] : Function.Injective (descendAut 3 F) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have hz : ∀ g : SpecialLinearGroup (Fin 3) F,
      ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F), e g = g * z := by
    intro g
    have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (proj 3 F g)) he
    simp only [descendAut_proj, MulAut.one_apply] at h
    refine ⟨g⁻¹ * e g, ?_, by group⟩
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h.symm
  have hle : commutator (SpecialLinearGroup (Fin 3) F) ≤
      MonoidHom.eqLocus (e : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
        (MonoidHom.id _) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨z₁, hz₁, ha⟩ := hz a
    obtain ⟨z₂, hz₂, hb⟩ := hz b
    show e ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ha, hb, commutatorElement_mul_central a b z₁ z₂ hz₁ hz₂]
  rw [CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := F) (n := 3)
    le_rfl] at hle
  refine MulEquiv.ext fun g => ?_
  exact hle (Subgroup.mem_top g)

theorem aut_cases [Finite F] (α : MulAut (SpecialLinearGroup (Fin 3) F)) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      α = CatalogueBHigherLinearAction.slConjugation 3 F A *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ *
          CatalogueBGraphForm.slGraphAut 3 F ^ ε := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, h⟩ := hgen (descendAut 3 F α)
  refine ⟨A, σ, ε, hε, descendAut_injective F ?_⟩
  rw [h, map_mul, map_mul, map_pow]
  rfl

@[expose] def mulVecAdd (A B : Matrix (Fin 3) (Fin 3) F) (hAB : A * B = 1) (hBA : B * A = 1) :
    (Fin 3 → F) ≃+ (Fin 3 → F) where
  toFun v := A *ᵥ v
  invFun v := B *ᵥ v
  left_inv v := by
    show B *ᵥ (A *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  right_inv v := by
    show A *ᵥ (B *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add A

@[expose] def mapAdd (σ : F ≃+* F) : (Fin 3 → F) ≃+ (Fin 3 → F) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

@[expose] def LinInd (β : MulAut (SpecialLinearGroup (Fin 3) F)) : Prop :=
  ∃ Θ : (Fin 3 → F) ≃+ (Fin 3 → F), ∀ (x : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
    Θ ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((β x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Θ v

theorem LinInd.mul {β₁ β₂ : MulAut (SpecialLinearGroup (Fin 3) F)} (h₁ : LinInd β₁)
    (h₂ : LinInd β₂) : LinInd (β₁ * β₂) := by
  obtain ⟨Θ₁, hΘ₁⟩ := h₁
  obtain ⟨Θ₂, hΘ₂⟩ := h₂
  refine ⟨Θ₂.trans Θ₁, fun x v => ?_⟩
  simp only [AddEquiv.trans_apply, MulAut.mul_apply]
  rw [hΘ₂, hΘ₁]

theorem LinInd.inv {β : MulAut (SpecialLinearGroup (Fin 3) F)} (h : LinInd β) :
    LinInd β⁻¹ := by
  obtain ⟨Θ, hΘ⟩ := h
  refine ⟨Θ.symm, fun y w => ?_⟩
  apply Θ.injective
  rw [AddEquiv.apply_symm_apply, hΘ, AddEquiv.apply_symm_apply]
  have : β (β⁻¹ y) = y := MulEquiv.apply_symm_apply β y
  rw [this]

theorem linInd_conj (g : SpecialLinearGroup (Fin 3) F) : LinInd (MulAut.conj g) := by
  have hAB : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBA : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨mulVecAdd _ _ hAB hBA, fun x v => ?_⟩
  change (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
    ((MulAut.conj g x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, MulAut.conj_apply,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, hBA, Matrix.mul_one]

theorem linInd_conj_field (A : GL (Fin 3) F) (σ : F ≃+* F) :
    LinInd (CatalogueBHigherLinearAction.slConjugation 3 F A *
      CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ) := by
  refine ⟨(mapAdd σ).trans (mulVecAdd _ _ (coe_mul_coe_inv A) (coe_inv_mul_coe A)),
    fun x v => ?_⟩
  change (A : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (fun i => σ (((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
    ((CatalogueBHigherLinearAction.slConjugation 3 F A
      (CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ x) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ (fun i => σ (v i)))
  rw [CatalogueBHigherLinearAction.slConjugation_matrix]
  have hσ : (fun i => σ (((x : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i)) =
      ((x : Matrix (Fin 3) (Fin 3) F).map σ) *ᵥ (fun i => σ (v i)) := by
    funext i
    exact RingHom.map_mulVec σ.toRingHom (x : Matrix (Fin 3) (Fin 3) F) v i
  rw [hσ]
  have hx : ((CatalogueBHigherLinearField.slFieldAut (Fin 3) F σ x :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (x : Matrix (Fin 3) (Fin 3) F).map σ := rfl
  rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
    coe_inv_mul_coe, Matrix.mul_one]

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} {g w : G} {S : Sylow p G} :
    w ∈ ((g • S : Sylow p G) : Subgroup G) ↔ g⁻¹ * w * g ∈ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv]

theorem exists_sq_ne_one [Finite F] [CharP F 2] (α₁ : MulAut (SpecialLinearGroup (Fin 3) F))
    (P₁ : Sylow 2 (SpecialLinearGroup (Fin 3) F)) (hP : ∀ x ∈ P₁, α₁ x ∈ P₁)
    (hinv : ∀ x, α₁ (α₁ x) = x) (hnot : ¬ LinInd α₁) :
    ∃ x ∈ P₁, (x⁻¹ * α₁ x) * (x⁻¹ * α₁ x) ≠ 1 := by
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) Q P₁
  have hmem : ∀ w : SpecialLinearGroup (Fin 3) F,
      w ∈ (P₁ : Subgroup (SpecialLinearGroup (Fin 3) F)) ↔ g⁻¹ * w * g ∈ unitriangular 3 F := by
    intro w
    rw [← hg, mem_smul_sylow_iff, hQ]
  set β : MulAut (SpecialLinearGroup (Fin 3) F) :=
    MulAut.conj g⁻¹ * α₁ * MulAut.conj g with hβdef
  have hβ : ∀ x, β x = g⁻¹ * α₁ (g * x * g⁻¹) * g := by
    intro x
    simp [hβdef, MulAut.conj_apply]
  have hβT : ∀ u ∈ unitriangular 3 F, β u ∈ unitriangular 3 F := by
    intro u hu
    rw [hβ]
    have h1 : g * u * g⁻¹ ∈ P₁ := (hmem _).mpr (by simpa [mul_assoc] using hu)
    exact (hmem _).mp (hP _ h1)
  have hβ2 : ∀ x, β (β x) = x := by
    intro x
    rw [hβ, hβ]
    have : g * (g⁻¹ * α₁ (g * x * g⁻¹) * g) * g⁻¹ = α₁ (g * x * g⁻¹) := by group
    rw [this, hinv]
    group
  have hnotβ : ¬ LinInd β := by
    intro h
    apply hnot
    have h' : LinInd (MulAut.conj g * β * (MulAut.conj g)⁻¹) :=
      ((linInd_conj g).mul h).mul (linInd_conj g).inv
    have : MulAut.conj g * β * (MulAut.conj g)⁻¹ = α₁ := by
      rw [hβdef, map_inv]
      group
    rwa [this] at h'
  obtain ⟨A, σ, ε, hε, hβform⟩ := aut_cases β
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exfalso
    apply hnotβ
    rw [hβform, pow_zero, mul_one]
    exact linInd_conj_field A σ
  · rw [pow_one] at hβform
    have hgr : β = graphAut A σ := hβform
    have hT' : ∀ u ∈ unitriangular 3 F, graphAut A σ u ∈ unitriangular 3 F := hgr ▸ hβT
    have hsq' : ∀ x, graphAut A σ (graphAut A σ x) = x := hgr ▸ hβ2
    have key := sq_ne_one_graphAut A σ hT' hsq'
    refine ⟨g * tri 1 0 0 * g⁻¹, ?_, ?_⟩
    · exact (hmem _).mpr (by simpa [mul_assoc] using tri_mem_unitriangular (1 : F) 0 0)
    · intro h
      apply key
      have e : α₁ (g * tri 1 0 0 * g⁻¹) = g * graphAut A σ (tri 1 0 0) * g⁻¹ := by
        rw [← hgr, hβ]
        group
      rw [e] at h
      have h2 : g * (((tri (1 : F) 0 0)⁻¹ * graphAut A σ (tri 1 0 0)) *
          ((tri (1 : F) 0 0)⁻¹ * graphAut A σ (tri 1 0 0))) * g⁻¹ = 1 := by
        rw [← h]
        group
      have h3 := congrArg (fun y => g⁻¹ * y * g) h2
      simpa [mul_assoc] using h3

end CFSG.Quasithin.G11.P4SL34
