module

public import CFSG.Quasithin.Vol2.Ch10SecALiftCore

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

variable {F : Type} [Field F] [CharP F 2] {M : Type} [CommGroup M]

omit [CharP F 2] in
theorem coe_inv_mul_SL (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

omit [CharP F 2] in
theorem coe_mul_inv_SL (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem fix_of_natural_conj (hM : ∀ m : M, m ^ 2 = 1)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut M) {Z : Subgroup M}
    (hZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z) (β : M →* Multiplicative (Fin 2 → F))
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 1 ↔ w ∈ Z)
    (hβe : ∀ γ w, β (ρ γ w) = Multiplicative.ofAdd
      ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β w))))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) {w : M}
    (hw : β (ρ (g⁻¹ * unipSL 1 * g) w) = β w) (b : F) : ρ (g⁻¹ * unipSL b * g) w = w := by
  set Mg : (Fin 2 → F) →+ (Fin 2 → F) :=
    (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom with hMg
  set β' : M →* Multiplicative (Fin 2 → F) := (AddMonoidHom.toMultiplicative Mg).comp β with hβ'
  have hβ'a : ∀ v, Multiplicative.toAdd (β' v) =
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β v)) := fun v => rfl
  set ρ' := ρ.comp (MulAut.conj g⁻¹).toMonoidHom with hρ'
  have hρ'a : ∀ γ, ρ' γ = ρ (g⁻¹ * γ * g) := fun γ => by
    rw [hρ']
    simp
  have hZ' : ∀ γ, ∀ z ∈ Z, ρ' γ z = z := fun γ z hz => by rw [hρ'a]; exact hZ _ z hz
  have hβ's : Function.Surjective β' := by
    intro m
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd m)))
    refine ⟨v, Multiplicative.toAdd.injective ?_⟩
    rw [hβ'a, hv, toAdd_ofAdd, Matrix.mulVec_mulVec, coe_mul_inv_SL, Matrix.one_mulVec]
  have hβ'k : ∀ v, β' v = 1 ↔ v ∈ Z := by
    intro v
    rw [← hβk]
    constructor
    · intro h
      apply Multiplicative.toAdd.injective
      have h1 := congrArg (fun m => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd m)) h
      simp only [hβ'a, Matrix.mulVec_mulVec, coe_inv_mul_SL, Matrix.one_mulVec, toAdd_one,
        Matrix.mulVec_zero] at h1
      rw [h1, toAdd_one]
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hβ'a, h, toAdd_one, Matrix.mulVec_zero]
  have hβ'e : ∀ γ v, β' (ρ' γ v) = Multiplicative.ofAdd
      ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β' v))) := by
    intro γ v
    apply Multiplicative.toAdd.injective
    rw [hβ'a, hρ'a, hβe, toAdd_ofAdd, toAdd_ofAdd, hβ'a, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      coe_mul_inv_SL, Matrix.one_mul]
  have hw1 : Multiplicative.toAdd (β' w) 1 = 0 := by
    have h1 := congrArg (fun m => (g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd m)) hw
    simp only [hβe, toAdd_ofAdd, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mul_assoc, coe_mul_inv_SL, Matrix.one_mul] at h1
    rw [← Matrix.mulVec_mulVec, coe_unipSL, unipSL_mulVec] at h1
    rw [hβ'a]
    have h2 := congrFun h1 0
    simp only [Matrix.cons_val_zero, one_mul] at h2
    linear_combination h2
  have := fix_of_natural hM ρ' hZ' β' hβ's hβ'k hβ'e hw1 b
  rwa [hρ'a] at this

end CFSG.Quasithin.Vol2.Ch10.SecA
