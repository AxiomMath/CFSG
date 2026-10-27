module

public import CFSG.Quasithin.Background.SzG11TensorB
public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

namespace G11

namespace SzG11S

namespace Tensor

open Matrix

section Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def transport
    (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V)
    (e : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[GaloisField 2 2]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) : GLV V :=
  zmodEquiv ((Θ.symm.toAddEquiv.trans e.toAddEquiv).trans Θ.toAddEquiv)

theorem transport_apply (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V)
    (e : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[GaloisField 2 2]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) (v : V) :
    transport Θ e v = Θ (e (Θ.symm v)) := rfl

@[expose] noncomputable def tensorAction
    (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V) :
    SpecialLinearGroup (Fin 2) (GaloisField 2 2) × SpecialLinearGroup (Fin 2) (GaloisField 2 2) →*
      GLV V where
  toFun z := transport Θ (P3Ortho.Om4.rho' (GaloisField 2 2) z)
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    rw [transport_apply, map_one]
    simp
  map_mul' z z' := by
    refine LinearEquiv.ext fun v => ?_
    rw [transport_apply, map_mul]
    show Θ ((P3Ortho.Om4.rho' (GaloisField 2 2) z) ((P3Ortho.Om4.rho' (GaloisField 2 2) z')
      (Θ.symm v))) = _
    rw [LinearEquiv.mul_apply, transport_apply, transport_apply, LinearEquiv.symm_apply_apply]

theorem tensorAction_apply (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V)
    (z : SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    tensorAction Θ z (Θ X) = Θ ((z.1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X *
      ((z.2⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2))) := by
  show transport Θ (P3Ortho.Om4.rho' (GaloisField 2 2) z) (Θ X) = _
  rw [transport_apply, LinearEquiv.symm_apply_apply]
  exact congrArg Θ (specialRho_apply z X)

theorem tensorAction_injective (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V) :
    Function.Injective (tensorAction Θ) := by
  intro z z' h
  apply P3Ortho.Om4.rho'_injective
  refine LinearEquiv.ext fun X => ?_
  have := congrArg (fun g : GLV V => Θ.symm (g (Θ X))) h
  simpa [tensorAction, transport_apply] using this

theorem four_le_card_galoisField : 4 ≤ Nat.card (GaloisField 2 2) := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem range_ortho_eq :
    ((P3Ortho.Om4.Ψ (GaloisField 2 2)).symm.toMonoidHom.comp
      (P3Ortho.Om4.rho' (GaloisField 2 2))).range =
      StatedOmega (StatedQuadPlus 2 (GaloisField 2 2)) := by
  have hΩ : (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))).map
      (P3Ortho.Om4.Ψ (GaloisField 2 2)).toMonoidHom =
      (P3Ortho.Om4.rho' (GaloisField 2 2)).range := by
    rw [P3Ortho.Om4.map_statedOmega, P3Ortho.Om4.commutator_eq_range four_le_card_galoisField]
  rw [MonoidHom.range_comp, ← hΩ, Subgroup.map_map]
  have : ((P3Ortho.Om4.Ψ (GaloisField 2 2)).symm.toMonoidHom.comp
      (P3Ortho.Om4.Ψ (GaloisField 2 2)).toMonoidHom) = MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem ortho_injective :
    Function.Injective ((P3Ortho.Om4.Ψ (GaloisField 2 2)).symm.toMonoidHom.comp
      (P3Ortho.Om4.rho' (GaloisField 2 2))) :=
  (P3Ortho.Om4.Ψ (GaloisField 2 2)).symm.injective.comp P3Ortho.Om4.rho'_injective

theorem isNaturalMatrixModule_of_tensor (H C : Subgroup (GLV V))
    (Θ : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2] V)
    (hH : ∀ h ∈ H, ∃ A : SpecialLinearGroup (Fin 2) (GaloisField 2 2), ∀ X,
      h (Θ X) = Θ ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X))
    (hH' : ∀ A : SpecialLinearGroup (Fin 2) (GaloisField 2 2), ∃ h ∈ H, ∀ X,
      h (Θ X) = Θ ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X))
    (hC : ∀ c ∈ C, ∃ B : SpecialLinearGroup (Fin 2) (GaloisField 2 2), ∀ X,
      c (Θ X) = Θ (X * ((B⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2))))
    (hC' : ∀ B : SpecialLinearGroup (Fin 2) (GaloisField 2 2), ∃ c ∈ C, ∀ X,
      c (Θ X) = Θ (X * ((B⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)))) :
    IsNaturalMatrixModule (H ⊔ C) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) := by
  have hleft : ∀ (h : GLV V) (A : SpecialLinearGroup (Fin 2) (GaloisField 2 2)),
      (∀ X, h (Θ X) = Θ ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * X)) →
      h = tensorAction Θ (A, 1) := by
    intro h A hA
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨X, rfl⟩ := Θ.surjective v
    rw [hA, tensorAction_apply]
    simp
  have hright : ∀ (c : GLV V) (B : SpecialLinearGroup (Fin 2) (GaloisField 2 2)),
      (∀ X, c (Θ X) = Θ (X * ((B⁻¹ : SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)))) → c = tensorAction Θ (1, B) := by
    intro c B hB
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨X, rfl⟩ := Θ.surjective v
    rw [hB, tensorAction_apply]
    simp
  have hrange : (tensorAction Θ).range = H ⊔ C := by
    apply le_antisymm
    · rintro _ ⟨⟨A, B⟩, rfl⟩
      obtain ⟨h, hh, hhA⟩ := hH' A
      obtain ⟨c, hc, hcB⟩ := hC' B
      have : tensorAction Θ (A, B) = h * c := by
        rw [hleft h A hhA, hright c B hcB, ← map_mul]
        simp
      rw [this]
      exact Subgroup.mul_mem_sup hh hc
    · refine sup_le ?_ ?_
      · intro h hh
        obtain ⟨A, hA⟩ := hH h hh
        exact ⟨(A, 1), (hleft h A hA).symm⟩
      · intro c hc
        obtain ⟨B, hB⟩ := hC c hc
        exact ⟨(1, B), (hright c B hB).symm⟩
  let e : (SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ≃* ↥(H ⊔ C) :=
    (MonoidHom.ofInjective (tensorAction_injective Θ)).trans (MulEquiv.subgroupCongr hrange)
  let eΩ : (SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ≃*
      ↥(StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) :=
    (MonoidHom.ofInjective ortho_injective).trans (MulEquiv.subgroupCongr range_ortho_eq)
  refine ⟨e.symm.trans eΩ,
    Θ.symm.trans (zmodEquiv (P3Ortho.Om4.toMat (GaloisField 2 2)).symm.toAddEquiv),
    fun g v => ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective g
  have hcoe : ((e z : ↥(H ⊔ C)) : GLV V) = tensorAction Θ z := rfl
  have hΩcoe : (((e.symm.trans eΩ) (e z) : ↥(StatedOmega (StatedQuadPlus 2 (GaloisField 2 2)))) :
      Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) =
      (P3Ortho.Om4.Ψ (GaloisField 2 2)).symm (P3Ortho.Om4.rho' (GaloisField 2 2) z) := by
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  rw [hΩcoe, hcoe]
  have h1 := P3Ortho.Om4.Ψ_apply (GaloisField 2 2)
    ((P3Ortho.Om4.Ψ (GaloisField 2 2)).symm (P3Ortho.Om4.rho' (GaloisField 2 2) z)) (Θ.symm v)
  rw [MulEquiv.apply_symm_apply] at h1
  show (P3Ortho.Om4.toMat (GaloisField 2 2)).symm (Θ.symm (tensorAction Θ z v)) = _
  have h2 : Θ.symm (tensorAction Θ z v) = P3Ortho.Om4.rho' (GaloisField 2 2) z (Θ.symm v) := by
    show Θ.symm (transport Θ (P3Ortho.Om4.rho' (GaloisField 2 2) z) v) = _
    rw [transport_apply, LinearEquiv.symm_apply_apply]
  rw [h2, h1, LinearEquiv.symm_apply_apply]
  rfl

end Assembly

end Tensor

end SzG11S

end G11

end CFSG.Quasithin
