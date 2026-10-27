module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.DualNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFourModules

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.CGT.PushingUpLit.CGT6.EmbModule
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem isNaturalModule_of_dual {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    (h : IsNaturalModule ρ.dual) : IsNaturalModule ρ := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨φ, hφ⟩ := h
  have hφnat : ∀ (g : SL(2, F)) (f : Module.Dual (ZMod 2) W),
      φ ((ρ.dual g) f) = natRep F g (φ f) := by
    intro g f
    rw [hφ g f, natRep_apply]
  let φL : Module.Dual (ZMod 2) W ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { toFun := φ
      invFun := φ.symm
      left_inv := φ.left_inv
      right_inv := φ.right_inv
      map_add' := φ.map_add
      map_smul' := fun c x => by
        rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl <;> simp }
  have hφL : ∀ x : Module.Dual (ZMod 2) W, φL x = φ x := fun _ => rfl
  have hφLs : ∀ n : Fin 2 → F, φL.symm n = φ.symm n := by
    intro n
    refine φL.injective ?_
    rw [LinearEquiv.apply_symm_apply, hφL, AddEquiv.apply_symm_apply]
  let T : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 2 → F) :=
    (Module.evalEquiv (ZMod 2) W).trans (φL.symm.dualMap)
  have hT_apply : ∀ (w : W) (n : Fin 2 → F), T w n = (φL.symm n) w := by
    intro w n
    simp only [T, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Module.evalEquiv_apply,
      Module.Dual.eval_apply]
  have hT : ∀ (g : SL(2, F)) (w : W), T (ρ g w) = (natRep F).dual g (T w) := by
    intro g w
    refine LinearMap.ext fun n => ?_
    rw [hT_apply]
    have h1 : (ρ.dual g⁻¹) (φL.symm n) = φL.symm (natRep F g⁻¹ n) := by
      refine φL.injective ?_
      calc φL ((ρ.dual g⁻¹) (φL.symm n))
          = φ ((ρ.dual g⁻¹) (φL.symm n)) := hφL _
        _ = natRep F g⁻¹ (φ (φL.symm n)) := hφnat g⁻¹ (φL.symm n)
        _ = natRep F g⁻¹ n := by rw [hφLs, AddEquiv.apply_symm_apply]
        _ = φL (φL.symm (natRep F g⁻¹ n)) := (LinearEquiv.apply_symm_apply φL _).symm
    have h2 : ((ρ.dual g⁻¹) (φL.symm n)) w = (φL.symm n) (ρ g w) := by
      rw [Representation.dual_apply, Module.Dual.transpose_apply, inv_inv]
      rfl
    have hR : ((natRep F).dual g (T w)) n = (T w) (natRep F g⁻¹ n) := by
      rw [Representation.dual_apply, Module.Dual.transpose_apply]
      rfl
    rw [hR, hT_apply, ← h2, h1]
  obtain ⟨Ψ, hΨ⟩ := natRep_dual_equiv F
  let ψ : W ≃+ (Fin 2 → F) := T.toAddEquiv.trans Ψ.symm
  refine ⟨ψ, fun g w => ?_⟩
  have hΨψ : Ψ (ψ w) = T w := by
    change Ψ (Ψ.symm (T w)) = T w
    rw [AddEquiv.apply_symm_apply]
  rw [← natRep_apply]
  calc ψ (ρ g w) = Ψ.symm (T (ρ g w)) := rfl
    _ = Ψ.symm ((natRep F).dual g (T w)) := by rw [hT]
    _ = Ψ.symm ((natRep F).dual g (Ψ (ψ w))) := by rw [hΨψ]
    _ = Ψ.symm (Ψ (natRep F g (ψ w))) := by rw [hΨ]
    _ = natRep F g (ψ w) := AddEquiv.symm_apply_apply Ψ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
