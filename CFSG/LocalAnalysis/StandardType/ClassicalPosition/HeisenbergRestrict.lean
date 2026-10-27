module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

theorem exists_restrictHom_of_invariant {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] (φ : G →* (V ≃ₗ[F] V)) (W : Submodule F V) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    ∃ ψ : G →* (W ≃ₗ[F] W), ∀ (g : G) (w : W), ((ψ g w : W) : V) = φ g w := by
  have hmap : ∀ g, W.map (φ g : V →ₗ[F] V) = W := by
    intro g
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hW g w hw
    · intro w hw
      refine ⟨φ g⁻¹ w, hW g⁻¹ w hw, ?_⟩
      rw [LinearEquiv.coe_coe, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  refine ⟨{ toFun := fun g => LinearEquiv.ofSubmodules (φ g) W W (hmap g)
            map_one' := ?_
            map_mul' := ?_ }, fun g w => rfl⟩
  · ext w
    simp
  · intro g h
    ext w
    simp

end CFSG.StandardType.ClassicalPosition.HeisRank
