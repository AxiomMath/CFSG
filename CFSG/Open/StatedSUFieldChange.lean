module

public import CFSG.Open.StatedDefs
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Open.StatedSUFieldChange

open Matrix

section FieldChange

variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂) (n q : ℕ)

@[expose] noncomputable def glEquiv : GL (Fin n) F₁ ≃* GL (Fin n) F₂ :=
  CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n) e

theorem glEquiv_coe (A : GL (Fin n) F₁) :
    ((glEquiv e n A : GL (Fin n) F₂) : Matrix (Fin n) (Fin n) F₂) =
      (A : Matrix (Fin n) (Fin n) F₁).map e := rfl

theorem statedSU_generator_iff (A : GL (Fin n) F₁) :
    ((glEquiv e n A : Matrix (Fin n) (Fin n) F₂).det = 1 ∧
      ((glEquiv e n A : Matrix (Fin n) (Fin n) F₂).map (· ^ q))ᵀ *
        (glEquiv e n A : Matrix (Fin n) (Fin n) F₂) = 1) ↔
    ((A : Matrix (Fin n) (Fin n) F₁).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) F₁).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) F₁) = 1) := by
  rw [glEquiv_coe]
  have hdet : ((A : Matrix (Fin n) (Fin n) F₁).map e).det =
      e (A : Matrix (Fin n) (Fin n) F₁).det := (RingHom.map_det e.toRingHom _).symm
  have hmat : (((A : Matrix (Fin n) (Fin n) F₁).map e).map (· ^ q))ᵀ *
      (A : Matrix (Fin n) (Fin n) F₁).map e =
      ((((A : Matrix (Fin n) (Fin n) F₁).map (· ^ q))ᵀ *
        (A : Matrix (Fin n) (Fin n) F₁)).map e) := by
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map]
    congr 2
    ext x
    simp [map_pow]
  rw [hdet, hmat]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨e.injective (by rw [h1, map_one]), ?_⟩
    have := congrArg (Matrix.map · e.symm) h2
    simpa [Matrix.map_map, Function.comp_def] using this
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1, map_one], ?_⟩
    rw [h2]
    exact Matrix.map_one _ (map_zero e) (map_one e)

theorem map_statedSU :
    (StatedSU n q F₁).map (glEquiv e n).toMonoidHom = StatedSU n q F₂ :=
  CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU e n q

theorem glEquiv_scalar (c : F₁ˣ) :
    glEquiv e n (Matrix.GeneralLinearGroup.scalar (Fin n) c) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.map e.toRingHom.toMonoidHom c) := by
  apply Units.ext
  ext i j
  rw [glEquiv_coe, Matrix.map_apply]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem map_statedScalars :
    (StatedScalars (Fin n) F₁).map (glEquiv e n).toMonoidHom = StatedScalars (Fin n) F₂ :=
  CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars (ι := Fin n) e

@[expose] noncomputable def statedSUEquiv : StatedSU n q F₁ ≃* StatedSU n q F₂ :=
  ((glEquiv e n).subgroupMap _).trans (MulEquiv.subgroupCongr (map_statedSU e n q))

theorem statedSUEquiv_coe (x : StatedSU n q F₁) :
    ((statedSUEquiv e n q x : StatedSU n q F₂) : GL (Fin n) F₂) = glEquiv e n x := rfl

@[expose] noncomputable def statedProjSUEquiv :
    StatedProj (StatedSU n q F₁) ≃* StatedProj (StatedSU n q F₂) :=
  QuotientGroup.congr _ _ (statedSUEquiv e n q) (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (glEquiv e n x) ∈ _
      rw [← map_statedScalars e n]
      exact ⟨x, hx, rfl⟩
    · intro hy
      refine ⟨(statedSUEquiv e n q).symm y, ?_, MulEquiv.apply_symm_apply _ y⟩
      rw [← map_statedScalars e n] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have : ((statedSUEquiv e n q).symm y : GL (Fin n) F₁) = x := by
        apply (glEquiv e n).injective
        rw [← statedSUEquiv_coe, MulEquiv.apply_symm_apply, ← hxy]
        rfl
      rw [this]
      exact hx)

end FieldChange

end CFSG.Open.StatedSUFieldChange
