module

public import CFSG.Quasithin.Background.Harris.Alt6.Heart
public import CFSG.Quasithin.Background.G12Stmts

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.CharacterTheory.SteinbergBY AlternatingSix Equiv Matrix CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def stdForm : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) :=
  Matrix.toBilin' heartForm

theorem stdForm_apply (x y : Fin 4 → ZMod 2) : stdForm x y = x ⬝ᵥ (heartForm *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem stdForm_alt : ∀ x : Fin 4 → ZMod 2, stdForm x x = 0 := by
  intro x
  rw [stdForm_apply]
  revert x
  decide

theorem stdForm_sep : ∀ x : Fin 4 → ZMod 2, (∀ y, stdForm x y = 0) → x = 0 := by
  simp only [stdForm_apply]
  decide

theorem stdForm_mulVec {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : Mᵀ * heartForm * M = heartForm)
    (x y : Fin 4 → ZMod 2) : stdForm (M *ᵥ x) (M *ᵥ y) = stdForm x y := by
  rw [stdForm_apply, stdForm_apply, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hM]

@[expose] noncomputable def transportForm (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) V :=
  stdForm.compl₁₂ T.toLinearMap T.toLinearMap

theorem transportForm_apply (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) (x y : V) :
    transportForm T x y = stdForm (T x) (T y) := rfl

theorem transportForm_isSymplectic (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :
    IsSymplectic (transportForm T) := by
  refine ⟨fun x => stdForm_alt _, fun x hx => T.injective ?_⟩
  rw [map_zero]
  refine stdForm_sep _ fun y => ?_
  simpa [transportForm_apply] using hx (T.symm y)

theorem transportForm_invariant {L : Subgroup (GLV V)} (T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (π : ↥L → Perm (Fin 6))
    (hT : ∀ (l : ↥L) (v : V), T ((l : GLV V) v) = heartHom (π l) *ᵥ T v) :
    L ≤ spSub (transportForm T) := fun l hl x y => by
  rw [transportForm_apply, transportForm_apply, hT ⟨l, hl⟩, hT ⟨l, hl⟩]
  exact stdForm_mulVec (heartHom_form _) _ _

theorem selfDual_of_invariant_form {L : Subgroup (GLV V)} {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.Nondegenerate) (hL : ∀ l ∈ L, ∀ x y : V, B (l x) (l y) = B x y) :
    SelfDual L ⊤ := by
  let s : ↥(⊤ : Submodule (ZMod 2) V) →ₗ[ZMod 2] V := Submodule.subtype ⊤
  refine ⟨B.compl₁₂ s s, ⟨fun x hx => ?_, fun y hy => ?_⟩, fun k hk i j i' j' hi hj => ?_⟩
  · apply Subtype.ext
    exact hB.1 x.1 fun z => hx ⟨z, trivial⟩
  · apply Subtype.ext
    exact hB.2 y.1 fun z => hy ⟨z, trivial⟩
  · simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, s]
    rw [← hi, ← hj]
    exact hL k hk _ _

end CFSG.Quasithin.G11.Harris.Alt6
