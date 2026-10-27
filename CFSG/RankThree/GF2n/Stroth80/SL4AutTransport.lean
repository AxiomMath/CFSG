module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix

private lemma inv_mul_coe {n : ℕ} {K : Type*} [Field K] (A : GL (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K)⁻¹ * (A : Matrix (Fin n) (Fin n) K) = 1 :=
  Matrix.nonsing_inv_mul (A := (A : Matrix (Fin n) (Fin n) K)) (Matrix.isUnits_det_units A)

private lemma mul_inv_coe {n : ℕ} {K : Type*} [Field K] (A : GL (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (A := (A : Matrix (Fin n) (Fin n) K)) (Matrix.isUnits_det_units A)

private noncomputable def transportAddEquiv {n : ℕ} {K : Type*} [Field K]
    (A : GL (Fin n) K) (σ : K ≃+* K) :
    (Fin n → K) ≃+ (Fin n → K) where
  toFun x := fun i => σ.symm ((((A : Matrix (Fin n) (Fin n) K)⁻¹ *ᵥ x)) i)
  invFun y := (A : Matrix (Fin n) (Fin n) K) *ᵥ fun j => σ (y j)
  left_inv x := by
    funext i
    dsimp only
    simp only [RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, mul_inv_coe, Matrix.one_mulVec]
  right_inv y := by
    funext i
    dsimp only
    rw [Matrix.mulVec_mulVec, inv_mul_coe, Matrix.one_mulVec]
    exact σ.symm_apply_apply (y i)
  map_add' x y := by
    funext i
    simp [Matrix.mulVec_add]

private lemma transportAddEquiv_mulVec_of_conj {n : ℕ} {K : Type*} [Field K]
    (A : GL (Fin n) K) (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) :
    transportAddEquiv A σ
        (((A : Matrix (Fin n) (Fin n) K) * M.map σ *
          (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x) =
      M *ᵥ transportAddEquiv A σ x := by
  funext i
  have hm : (A : Matrix (Fin n) (Fin n) K)⁻¹ *
      ((A : Matrix (Fin n) (Fin n) K) * M.map σ *
        (A : Matrix (Fin n) (Fin n) K)⁻¹) =
      M.map σ * (A : Matrix (Fin n) (Fin n) K)⁻¹ := by
    rw [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left (A := (A : Matrix (Fin n) (Fin n) K)) (M.map σ)
      (Matrix.isUnits_det_units A)]
  calc transportAddEquiv A σ
        (((A : Matrix (Fin n) (Fin n) K) * M.map σ *
          (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x) i
      = σ.symm (((A : Matrix (Fin n) (Fin n) K)⁻¹ *ᵥ
          (((A : Matrix (Fin n) (Fin n) K) * M.map σ *
            (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x)) i) := rfl
    _ = σ.symm ((((A : Matrix (Fin n) (Fin n) K)⁻¹ *
          ((A : Matrix (Fin n) (Fin n) K) * M.map σ *
            (A : Matrix (Fin n) (Fin n) K)⁻¹)) *ᵥ x) i) := by
          rw [Matrix.mulVec_mulVec]
    _ = σ.symm (((M.map σ * (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x) i) := by rw [hm]
    _ = σ.symm (((M.map σ) *ᵥ
          ((A : Matrix (Fin n) (Fin n) K)⁻¹ *ᵥ x)) i) := by
          rw [← Matrix.mulVec_mulVec]
    _ = ((((M.map σ).map σ.symm) *ᵥ
          (σ.symm ∘ ((A : Matrix (Fin n) (Fin n) K)⁻¹ *ᵥ x))) i) :=
          RingHom.map_mulVec (σ.symm : K →+* K) (M.map σ)
            ((A : Matrix (Fin n) (Fin n) K)⁻¹ *ᵥ x) i
    _ = (M *ᵥ transportAddEquiv A σ x) i := by
          have hM : (M.map σ).map σ.symm = M := by
            ext j k
            simp
          rw [hM]
          rfl

theorem exists_addEquiv_typing_of_ker_eq {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {R : Type*} [Group R] (η₁ η₂ : R →* Matrix.SpecialLinearGroup (Fin n) K)
    (h₁ : Function.Surjective η₁) (h₂ : Function.Surjective η₂)
    (hker : ∀ r, η₁ r = 1 ↔ η₂ r = 1) :
    ∃ f : (Fin n → K) ≃+ (Fin n → K),
      (∀ (r : R) (x : Fin n → K), f (η₁ r • x) = η₂ r • f x) ∨
      (∀ (r : R) (x : Fin n → K),
        f (η₁ r • x) = Matrix.SpecialLinearGroup.transpose (η₂ r)⁻¹ • f x) := by
  have hker_eq : η₁.ker = η₂.ker := by
    ext r
    simp [MonoidHom.mem_ker, hker r]
  let β : MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
    (QuotientGroup.quotientKerEquivOfSurjective η₂ h₂).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective η₁ h₁))
  have hβ : ∀ r, η₁ r = β (η₂ r) := by
    intro r
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective η₂ h₂).symm (η₂ r) =
        (QuotientGroup.mk r : R ⧸ η₂.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change η₁ r = (QuotientGroup.quotientKerEquivOfSurjective η₁ h₁)
      ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm)
        ((QuotientGroup.quotientKerEquivOfSurjective η₂ h₂).symm (η₂ r)))
    rw [h1]
    rfl
  obtain ⟨A, σ, hcase | hcase⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hn β
  · refine ⟨transportAddEquiv A σ, ?_⟩
    left
    intro r x
    have hx : η₁ r • x =
        (((A : Matrix (Fin n) (Fin n) K) * ((η₂ r : Matrix (Fin n) (Fin n) K).map σ) *
          (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x) := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, hβ r, hcase (η₂ r),
        Matrix.GeneralLinearGroup.coe_inv]
    rw [hx, transportAddEquiv_mulVec_of_conj]
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  · refine ⟨transportAddEquiv A σ, ?_⟩
    right
    intro r x
    have hx : η₁ r • x =
        (((A : Matrix (Fin n) (Fin n) K) *
          ((((η₂ r)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K).transpose.map σ) *
          (A : Matrix (Fin n) (Fin n) K)⁻¹) *ᵥ x) := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, hβ r, hcase (η₂ r),
        Matrix.GeneralLinearGroup.coe_inv]
    rw [hx, transportAddEquiv_mulVec_of_conj]
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    rfl

theorem exists_sl4_common_typing {K : Type*} [Field K] [Finite K] [CharP K 2]
    {R L T : Type*} [Group R] [Group L] [AddCommGroup T] [Module K T]
    (η₁ η₂ : R →* Matrix.SpecialLinearGroup (Fin 4) K)
    (h₁ : Function.Surjective η₁) (h₂ : Function.Surjective η₂)
    (hker : ∀ r, η₁ r = 1 ↔ η₂ r = 1)
    (relL : R → L → L → Prop) (θ₁ : L →* Multiplicative (Fin 4 → K))
    (hθ₁s : Function.Surjective θ₁)
    (hθ₁ : ∀ r l l', relL r l l' →
      Multiplicative.toAdd (θ₁ l') = η₁ r • Multiplicative.toAdd (θ₁ l))
    (relT : R → T → T → Prop) (ψ₂ : T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (hψ₂ : ∀ r w w', relT r w w' →
      ψ₂ w' = CFSG.RankThree.PartOne.K159.Klein.rho (η₂ r) (ψ₂ w)) :
    ∃ η : R →* Matrix.SpecialLinearGroup (Fin 4) K,
      Function.Surjective η ∧ (∀ r, η r = 1 ↔ η₂ r = 1) ∧
      (∃ θ : L →* Multiplicative (Fin 4 → K),
        Function.Surjective θ ∧ (∀ l, θ l = 1 ↔ θ₁ l = 1) ∧
        ∀ r l l', relL r l l' →
          Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l)) ∧
      ∃ ψ : T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K),
        ∀ r w w', relT r w w' → ψ w' = CFSG.RankThree.PartOne.K159.Klein.rho (η r) (ψ w) := by
  obtain ⟨f, hf⟩ :=
    exists_addEquiv_typing_of_ker_eq (by norm_num : 3 ≤ 4) η₁ η₂ h₁ h₂ hker
  let θ : L →* Multiplicative (Fin 4 → K) :=
    (AddEquiv.toMultiplicative f).toMonoidHom.comp θ₁
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨l, hl⟩ := hθ₁s (Multiplicative.ofAdd (f.symm (Multiplicative.toAdd y)))
    refine ⟨l, ?_⟩
    change AddEquiv.toMultiplicative f (θ₁ l) = y
    rw [hl]
    simp
  have hθk : ∀ l, θ l = 1 ↔ θ₁ l = 1 := by
    intro l
    change AddEquiv.toMultiplicative f (θ₁ l) = 1 ↔ θ₁ l = 1
    exact MulEquiv.map_eq_one_iff _
  have hθrel : ∀ (η : R →* Matrix.SpecialLinearGroup (Fin 4) K),
      (∀ r x, f (η₁ r • x) = η r • f x) →
      ∀ r l l', relL r l l' →
        Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l) := by
    intro η hη r l l' h
    change f (Multiplicative.toAdd (θ₁ l')) =
      η r • f (Multiplicative.toAdd (θ₁ l))
    rw [hθ₁ r l l' h]
    exact hη r _
  rcases hf with hf | hf
  · refine ⟨η₂, h₂, fun _ => Iff.rfl, ⟨θ, hθs, hθk, hθrel η₂ hf⟩, ⟨ψ₂, hψ₂⟩⟩
  · let η : R →* Matrix.SpecialLinearGroup (Fin 4) K :=
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 K).toMonoidHom.comp η₂
    have hηs : Function.Surjective η := by
      simpa [η] using
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 K).surjective.comp h₂
    have hηk : ∀ r, η r = 1 ↔ η₂ r = 1 := by
      intro r
      change CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 K (η₂ r) = 1 ↔
        η₂ r = 1
      exact MulEquiv.map_eq_one_iff _
    have hηf : ∀ r x, f (η₁ r • x) = η r • f x := by
      intro r x
      rw [hf r x]
      rfl
    let J : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
      LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin 3) (Fin 3))
    let ψ : T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) := ψ₂.trans J
    have hJ : ∀ (g : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K),
        J (CFSG.RankThree.PartOne.K159.Klein.rho g v) =
          CFSG.RankThree.PartOne.K159.Klein.rho
            (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 K g) (J v) := by
      intro g v
      rw [CFSG.RankThree.PartOne.K159.Klein.rho_apply,
        CFSG.RankThree.PartOne.K159.Klein.rho_apply]
      rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
      exact (CFSG.SeitzReduction.OmegaPilot.cong_inverseTranspose_star g v).symm
    refine ⟨η, hηs, hηk, ⟨θ, hθs, hθk, hθrel η hηf⟩, ⟨ψ, ?_⟩⟩
    intro r w w' h
    change J (ψ₂ w') = CFSG.RankThree.PartOne.K159.Klein.rho (η r) (J (ψ₂ w))
    rw [hψ₂ r w w' h]
    exact hJ (η₂ r) (ψ₂ w)

end CFSG.RankThree.GF2n.Stroth80
