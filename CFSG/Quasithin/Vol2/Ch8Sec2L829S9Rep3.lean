module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Rep2

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix Module
open scoped MatrixGroups

section Bridge

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private lemma s9rPsi_s9P1 {A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)}
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X)) (F : Module.End A W) :
    s9rPsi σ ε (s9P1 F) = s9P1 (s9rPsi σ ε F) := by
  simp only [s9P1, map_add, map_mul, map_one]

private lemma s9r_ker_iff_isUnit (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (x : W ≃ₗ[ZMod 2] W) (F : Module.End A W) (hF : ∀ w, F w = (x : W →ₗ[ZMod 2] W) w) :
    LinearMap.ker (s9P1 (x : W →ₗ[ZMod 2] W)) = ⊥ ↔ IsUnit (s9P1 F) := by
  have hfun : ⇑(s9P1 F) = ⇑(s9P1 (x : W →ₗ[ZMod 2] W)) := by
    funext w
    simp only [s9P1, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, hF]
  rw [LinearMap.ker_eq_bot, Module.End.isUnit_iff, hfun, Finite.injective_iff_bijective]

theorem s9r_bridge (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ} (σ : Module.End A X ≃+* E)
    (ε : W ≃ₗ[A] (Fin d → ↥X)) (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W))
    (x : ↥G') :
    LinearMap.ker (s9P1 ((x : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) = ⊥ ↔
      (s9P1 ((s9rPhi A σ ε G' hG' x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det ≠ 0 := by
  obtain ⟨F, hFdef⟩ : ∃ F : Module.End A W,
      F = ((s9rHom A G' hG' x : W ≃ₗ[A] W) : Module.End A W) := ⟨_, rfl⟩
  have hF : ∀ w, F w = (x : W ≃ₗ[ZMod 2] W) w := fun w => by
    rw [hFdef] <;> rfl
  have hval : ((s9rPhi A σ ε G' hG' x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) =
      s9rPsi σ ε F := by
    rw [s9rPhi_val, hFdef]
  have hunit : IsUnit (s9P1 F) ↔ IsUnit (s9P1 (s9rPsi σ ε F)) := by
    rw [← s9rPsi_s9P1]
    exact (MulEquiv.isUnit_map (s9rPsi σ ε)).symm
  rw [s9r_ker_iff_isUnit A (x : W ≃ₗ[ZMod 2] W) F hF, hval, hunit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

end Bridge

end CFSG.Quasithin.H13.L829N
