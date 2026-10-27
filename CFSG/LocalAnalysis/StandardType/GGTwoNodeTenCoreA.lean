module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTen_sub_mem_span {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r)) :
    ∀ g ∈ A, ∀ w, g w - w ∈ Submodule.span (ZMod 3) (Set.range h) := by
  intro g hg w
  rw [hA] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ w, g w - w ∈ Submodule.span (ZMod 3) (Set.range h))
    ?_ ?_ ?_ ?_ hg w
  · rintro _ ⟨i, rfl⟩ w
    rw [hr i w, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · intro w
    simp
  · intro g g' _ _ ihg ihg' w
    rw [LinearEquiv.mul_apply]
    have h1 := Submodule.add_mem _ (ihg (g' w)) (ihg' w)
    rwa [sub_add_sub_cancel] at h1
  · intro g _ ihg w
    have h1 := ihg (g⁻¹ w)
    have h2 : g (g⁻¹ w) = w := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [h2] at h1
    rw [← neg_sub]
    exact Submodule.neg_mem _ h1

theorem ggTen_faithful {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] {ι : Type} (h : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (r : ι → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hA : A = Subgroup.closure (Set.range r))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hV : Module.finrank (ZMod 3) V ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) + 1) :
    ∀ g ∈ A, (∀ u ∈ Submodule.span (ZMod 3) (Set.range h), g u = u) → g = 1 := by
  intro g hg hfix
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hker_ge : Submodule.span (ZMod 3) (Set.range h) ≤
      LinearMap.ker (g.toLinearMap - LinearMap.id) := by
    intro u hu
    rw [LinearMap.mem_ker]
    exact sub_eq_zero.mpr (hfix u hu)
  have hdim := LinearMap.finrank_range_add_finrank_ker (g.toLinearMap - LinearMap.id)
  have hmono := Submodule.finrank_mono hker_ge
  have hle1 : Module.finrank (ZMod 3) (LinearMap.range (g.toLinearMap - LinearMap.id)) ≤ 1 := by
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
  · have hbot : LinearMap.range (g.toLinearMap - LinearMap.id) = ⊥ :=
      (Submodule.finrank_eq_zero).mp h0
    have hN : g.toLinearMap - LinearMap.id = 0 := LinearMap.range_eq_bot.mp hbot
    ext x
    have hx := congrArg (fun f : V →ₗ[ZMod 3] V => f x) hN
    simpa using sub_eq_zero.mp hx
  · exfalso
    exact hnt g hg ⟨by rw [ggLinMove]; exact h1,
      fun w => hfix (g w - w) (ggTen_sub_mem_span h α r hr A hA g hg w)⟩

end CFSG.StandardType

end
