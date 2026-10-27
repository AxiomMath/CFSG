module

public import CFSG.LocalAnalysis.StandardType.ZS.Support

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem apply_mem_commutatorSpace {H : Subgroup (U ≃ₗ[K] U)} {h : U ≃ₗ[K] U} (hh : h ∈ H)
    {v : U} (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    h v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  have key : HardMathSupport.Kantor79.commutatorSpace H ≤
      (HardMathSupport.Kantor79.commutatorSpace H).comap (h : U →ₗ[K] U) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, hg, u, rfl⟩
    have h1 : (h * g) u - u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.subset_span ⟨h * g, H.mul_mem hh hg, u, rfl⟩
    have h2 : h u - u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.subset_span ⟨h, hh, u, rfl⟩
    have heq : h (g u - u) = (h * g) u - u - (h u - u) := by
      rw [map_sub, LinearEquiv.mul_apply]
      abel
    change h (g u - u) ∈ HardMathSupport.Kantor79.commutatorSpace H
    rw [heq]
    exact sub_mem h1 h2
  exact key hv

@[expose] def restrictHom (H : Subgroup (U ≃ₗ[K] U)) (W : Submodule K U)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) : H →* (W ≃ₗ[K] W) where
  toFun h := (h : U ≃ₗ[K] U).ofSubmodules W W (map_eq_self_of_invariant hW h.2)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[simp]
theorem restrictHom_apply (H : Subgroup (U ≃ₗ[K] U)) (W : Submodule K U)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) (h : H) (w : W) :
    ((restrictHom H W hW h w : W) : U) = (h : U ≃ₗ[K] U) w :=
  rfl

@[expose] def movedGroup (H : Subgroup (U ≃ₗ[K] U)) :
    Subgroup (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[K]
      HardMathSupport.Kantor79.commutatorSpace H) :=
  (restrictHom H _ fun _ hh _ hv => apply_mem_commutatorSpace hh hv).range

end Field

@[expose] def IsOrthType (p : ℕ) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (A : Subgroup (W ≃ₗ[ZMod p] W)) : Prop :=
  ∃ Q : QuadraticForm (ZMod p) W, (QuadraticMap.polarBilin Q).Nondegenerate ∧
    ((∀ g, g ∈ A ↔ IsIsom p Q g) ∨
      ∃ c : ZMod p, c ≠ 0 ∧ A = Subgroup.closure (ClassRefl p Q c))

end CFSG.StandardType.ZS

end
