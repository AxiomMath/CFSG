module

public import CFSG.ClassicalInvolution.RouteD.GapsD4A

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups Matrix


variable {F F' : Type} [Field F] [Field F']

theorem linAutClass_of_ringEquiv (r : F ≃+* F') {n : ℕ} (h : LinearAutClassification F n) :
    LinearAutClassification F' n := by
  intro X _ θ' hθ' hker' σ
  set m : SL(n, F) →* SL(n, F') := Matrix.SpecialLinearGroup.map (n := Fin n) (r : F →+* F') with hm
  set m' : SL(n, F') →* SL(n, F) :=
    Matrix.SpecialLinearGroup.map (n := Fin n) (r.symm : F' →+* F) with hm'
  have hmm' : ∀ y, m (m' y) = y := fun y => by
    ext i j
    simp [hm, hm', Matrix.SpecialLinearGroup.map_apply_coe]
  have hm'm : ∀ x, m' (m x) = x := fun x => by
    ext i j
    simp [hm, hm', Matrix.SpecialLinearGroup.map_apply_coe]
  have hθ : Function.Surjective (θ'.comp m) := hθ'.comp (fun y => ⟨m' y, hmm' y⟩)
  have hker : (θ'.comp m).ker ≤ Subgroup.center SL(n, F) := by
    intro x hx
    have hx' : m x ∈ Subgroup.center SL(n, F') := hker' hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    have := hx' (m y)
    rw [← map_mul, ← map_mul] at this
    have := congrArg m' this
    simpa [hm'm] using this
  obtain ⟨α, g, φ, ε, hα, hform⟩ := h X (θ'.comp m) hθ hker σ
  refine ⟨m.comp (α.comp m'), Matrix.GeneralLinearGroup.map (r : F →+* F') g,
    r.symm.trans (φ.trans r), ε, ?_, ?_⟩
  · intro x
    have := hα (m' x)
    simp only [MonoidHom.comp_apply, hmm'] at this ⊢
    exact this
  · intro x
    have hA : ∀ (g : GL (Fin n) F), ((Matrix.GeneralLinearGroup.map (r : F →+* F') g :
        GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = r.mapMatrix (g : Matrix (Fin n) (Fin n) F) :=
      fun g => by
        ext i j
        simp [Matrix.GeneralLinearGroup.map_apply, RingEquiv.mapMatrix_apply]
    have hB : ((((Matrix.GeneralLinearGroup.map (r : F →+* F') g)⁻¹ : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F')) = r.mapMatrix ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← map_inv]; exact hA _
    have hC : ∀ M : Matrix (Fin n) (Fin n) F', (r.symm.trans (φ.trans r)).mapMatrix M =
        r.mapMatrix (φ.mapMatrix (r.symm.mapMatrix M)) := fun M => by
      ext i j
      simp [RingEquiv.mapMatrix_apply]
    have hD : r.symm.mapMatrix (if ε then (((x⁻¹ : SL(n, F')) : Matrix (Fin n) (Fin n) F'))ᵀ
        else (x : Matrix (Fin n) (Fin n) F')) =
        (if ε then (((m' x)⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ
          else ((m' x : SL(n, F)) : Matrix (Fin n) (Fin n) F)) := by
      cases ε
      · ext i j
        simp [hm', Matrix.SpecialLinearGroup.map_apply_coe, RingEquiv.mapMatrix_apply]
      · ext i j
        simp [hm', Matrix.SpecialLinearGroup.map_apply_coe, RingEquiv.mapMatrix_apply,
          ← map_inv]
    have hform' := hform (m' x)
    calc (((m.comp (α.comp m')) x : SL(n, F')) : Matrix (Fin n) (Fin n) F')
        = r.mapMatrix ((α (m' x) : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
          simp [hm, Matrix.SpecialLinearGroup.map_apply_coe]
      _ = _ := by
        rw [hform', map_mul, map_mul, hA, hB, hC, hD]


end CFSG.Quasithin.Background.Harris.KFact2d
