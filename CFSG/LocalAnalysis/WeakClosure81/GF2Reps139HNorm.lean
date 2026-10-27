module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open scoped Matrix

private theorem w1369_norm_bilin {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (Kb : Subgroup (V ≃ₗ[E] V))
    (habs : ∀ f : V →ₗ[E] V, (∀ k ∈ Kb, ∀ x, f (k x) = k (f x)) →
      ∃ c : E, ∀ x, f x = c • x)
    (b : LinearMap.BilinForm E V) (hb : b.Nondegenerate)
    (hinv : ∀ k ∈ Kb, ∀ x y, b (k x) (k y) = b x y) (g : V ≃ₗ[E] V)
    (hg : ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb) :
    ∃ l : E, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y := by
  classical
  let b' : LinearMap.BilinForm E V := b.compl₁₂ (g : V →ₗ[E] V) (g : V →ₗ[E] V)
  have hb'inv : ∀ k ∈ Kb, ∀ x y, b' (k x) (k y) = b' x y := by
    intro k hk x y
    have hk' : g * k * g.symm ∈ Kb := hg k hk
    have hgk : ∀ z, g (k z) = (g * k * g.symm) (g z) := by
      intro z
      rw [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.mul_apply]
    calc b' (k x) (k y) = b (g (k x)) (g (k y)) := rfl
      _ = b ((g * k * g.symm) (g x)) ((g * k * g.symm) (g y)) := by rw [hgk x, hgk y]
      _ = b (g x) (g y) := hinv (g * k * g.symm) hk' (g x) (g y)
      _ = b' x y := rfl
  let T : V →ₗ[E] V := (b.flip.toDual hb.flip).symm.toLinearMap ∘ₗ b'.flip
  have hT : ∀ x y, b x (T y) = b' x y := by
    intro x y
    change b.flip ((b.flip.toDual hb.flip).symm (b'.flip y)) x = b' x y
    rw [LinearMap.BilinForm.apply_toDual_symm_apply, LinearMap.BilinForm.flip_apply]
  have hTcomm : ∀ k ∈ Kb, ∀ y, T (k y) = k (T y) := by
    intro k hk y
    have hzero : T (k y) - k (T y) = 0 := by
      apply hb.2
      intro x
      have h1 : b' x (k y) = b' (k.symm x) y := by
        have h := hb'inv k hk (k.symm x) y
        rwa [LinearEquiv.apply_symm_apply] at h
      have h2 : b x (k (T y)) = b' (k.symm x) y := by
        rw [← hT (k.symm x) y]
        simpa using hinv k hk (k.symm x) (T y)
      rw [LinearMap.BilinForm.sub_right, hT x (k y), h1, ← h2, sub_self]
    exact sub_eq_zero.mp hzero
  obtain ⟨c, hc⟩ := habs T hTcomm
  by_cases hc0 : c = 0
  · haveI : Subsingleton V := by
      refine ⟨fun u v => ?_⟩
      have hz : u - v = 0 := by
        apply hb.2
        intro x
        obtain ⟨x', hx'⟩ := g.surjective x
        rw [← hx']
        obtain ⟨y, hy⟩ := g.surjective (u - v)
        rw [← hy]
        change b' x' y = 0
        rw [← hT x' y, hc y, hc0, zero_smul, map_zero]
      exact sub_eq_zero.mp hz
    refine ⟨1, one_ne_zero, fun x y => ?_⟩
    have hy : y = 0 := Subsingleton.elim y 0
    have hgy : g y = 0 := Subsingleton.elim (g y) 0
    rw [hgy, hy]
    simp
  · refine ⟨c, hc0, fun x y => ?_⟩
    change b' x y = c * b x y
    rw [← hT x y, hc y]
    exact LinearMap.BilinForm.smul_right c x y

theorem normalizer_preserves_alt {E V : Type} [Field E] [Finite E] [CharP E 2] [AddCommGroup V]
    [Module E V] [Module.Finite E V] (Kb : Subgroup (V ≃ₗ[E] V))
    (hirr : ∀ S : Submodule E V, (∀ k ∈ Kb, ∀ x ∈ S, k x ∈ S) → S = ⊥ ∨ S = ⊤)
    (habs : ∀ f : V →ₗ[E] V, (∀ k ∈ Kb, ∀ x, f (k x) = k (f x)) → ∃ c : E, ∀ x, f x = c • x)
    (b : LinearMap.BilinForm E V) (hb : b.Nondegenerate)
    (hinv : ∀ k ∈ Kb, ∀ x y, b (k x) (k y) = b x y) (g : V ≃ₗ[E] V)
    (hg : ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb) : ∃ l : E, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y :=
  w1369_norm_bilin Kb habs b hb hinv g hg

theorem normalizer_preserves_herm {E V : Type} [Field E] [Finite E] [CharP E 2] [AddCommGroup V]
    [Module E V] [Module.Finite E V] (θ : E →+* E) (Kb : Subgroup (V ≃ₗ[E] V))
    (hirr : ∀ S : Submodule E V, (∀ k ∈ Kb, ∀ x ∈ S, k x ∈ S) → S = ⊥ ∨ S = ⊤)
    (habs : ∀ f : V →ₗ[E] V, (∀ k ∈ Kb, ∀ x, f (k x) = k (f x)) → ∃ c : E, ∀ x, f x = c • x)
    (h : V →ₗ[E] V →ₛₗ[θ] E) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (hherm : ∀ x y, h y x = θ (h x y))
    (hinv : ∀ k ∈ Kb, ∀ x y, h (k x) (k y) = h x y) (g : V ≃ₗ[E] V)
    (hg : ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb) : ∃ l : E, l ≠ 0 ∧ ∀ x y, h (g x) (g y) = l * h x y := by
  classical
  let φ : V → Module.Dual E V := fun y =>
    { toFun := fun x => h (g x) (g y)
      map_add' := fun x₁ x₂ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun a x => by
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let Λ : V → Module.Dual E V := fun z =>
    { toFun := fun x => h x z
      map_add' := fun x₁ x₂ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun a x => by
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hΛinj : Function.Injective Λ := by
    intro z₁ z₂ hz
    have hz' : ∀ x, h x z₁ = h x z₂ :=
      fun x => congrArg (fun f : Module.Dual E V => f x) hz
    have hz'' : ∀ y, h z₁ y = h z₂ y := by
      intro y
      rw [hherm y z₁, hherm y z₂, hz' y]
    have hzero : z₁ - z₂ = 0 := by
      apply hnd
      intro y
      rw [map_sub, LinearMap.sub_apply, hz'' y, sub_self]
    exact sub_eq_zero.mp hzero
  haveI : Finite V := Module.finite_of_finite E
  let e : V ≃ Module.Dual E V :=
    (LinearEquiv.ofFinrankEq (M := V) (M' := Module.Dual E V)
      Subspace.dual_finrank_eq.symm).toEquiv
  have hΛsurj : Function.Surjective Λ :=
    (Finite.injective_iff_surjective_of_equiv e).mp hΛinj
  let Tfun : V → V := fun y => Classical.choose (hΛsurj (φ y))
  have hT : ∀ x y, h x (Tfun y) = h (g x) (g y) := by
    intro x y
    exact congrArg (fun f : Module.Dual E V => f x)
      (Classical.choose_spec (hΛsurj (φ y)))
  have hTadd : ∀ y z, Tfun (y + z) = Tfun y + Tfun z := by
    intro y z
    have hzero : Tfun (y + z) - (Tfun y + Tfun z) = 0 := by
      apply hnd
      intro w
      have hwa : h w (Tfun (y + z) - (Tfun y + Tfun z)) = 0 := by
        simp only [map_sub, hT w (y + z), map_add, hT w y, hT w z, sub_self]
      rw [hherm w (Tfun (y + z) - (Tfun y + Tfun z)), hwa, map_zero]
    exact sub_eq_zero.mp hzero
  have hTsmul : ∀ (c : E) (y : V), Tfun (c • y) = c • Tfun y := by
    intro c y
    have hzero : Tfun (c • y) - c • Tfun y = 0 := by
      apply hnd
      intro w
      have hwa : h w (Tfun (c • y) - c • Tfun y) = 0 := by
        simp only [map_sub, hT w (c • y), map_smul, LinearMap.map_smulₛₗ, hT w y, sub_self]
      rw [hherm w (Tfun (c • y) - c • Tfun y), hwa, map_zero]
    exact sub_eq_zero.mp hzero
  let T : V →ₗ[E] V :=
    { toFun := Tfun
      map_add' := hTadd
      map_smul' := hTsmul }
  have hT' : ∀ x y, h x (T y) = h (g x) (g y) := hT
  have hTcomm : ∀ k ∈ Kb, ∀ y, T (k y) = k (T y) := by
    intro k hk y
    have hh'inv : ∀ x y, h (g (k x)) (g (k y)) = h (g x) (g y) := by
      intro x y
      have hk' : g * k * g.symm ∈ Kb := hg k hk
      have hgk : ∀ z, g (k z) = (g * k * g.symm) (g z) := by
        intro z
        rw [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.mul_apply]
      calc h (g (k x)) (g (k y))
          = h ((g * k * g.symm) (g x)) ((g * k * g.symm) (g y)) := by rw [hgk x, hgk y]
        _ = h (g x) (g y) := hinv (g * k * g.symm) hk' (g x) (g y)
    have hzero : T (k y) - k (T y) = 0 := by
      apply hnd
      intro w
      have hkinv : h w (k (T y)) = h (g (k.symm w)) (g y) := by
        have h1 := hinv k hk (k.symm w) (T y)
        rw [LinearEquiv.apply_symm_apply] at h1
        rw [← hT' (k.symm w) y, ← h1]
      have hkw : h (g w) (g (k y)) = h (g (k.symm w)) (g y) := by
        have h2 := hh'inv (k.symm w) y
        rwa [LinearEquiv.apply_symm_apply] at h2
      have hwa : h w (T (k y) - k (T y)) = 0 := by
        rw [map_sub, hT' w (k y), hkinv, hkw, sub_self]
      rw [hherm w (T (k y) - k (T y)), hwa, map_zero]
    exact sub_eq_zero.mp hzero
  obtain ⟨c, hc⟩ := habs T hTcomm
  by_cases hc0 : c = 0
  · haveI : Subsingleton V := by
      refine ⟨fun u v => ?_⟩
      have hz : u - v = 0 := by
        apply hnd
        intro y
        obtain ⟨x, hx⟩ := g.surjective (u - v)
        rw [← hx]
        obtain ⟨y', hy'⟩ := g.surjective y
        rw [← hy']
        rw [← hT' x y', hc y', hc0, zero_smul, map_zero]
      exact sub_eq_zero.mp hz
    refine ⟨1, one_ne_zero, fun x y => ?_⟩
    have hy : y = 0 := Subsingleton.elim y 0
    have hgy : g y = 0 := Subsingleton.elim (g y) 0
    rw [hgy, hy]
    simp
  · refine ⟨θ c, ?_, fun x y => ?_⟩
    · intro hθc
      have h1 : (1 : E) = 0 := by
        rw [← map_one θ, ← mul_inv_cancel₀ hc0, map_mul, hθc, zero_mul]
      exact one_ne_zero h1
    · rw [← hT' x y, hc y]
      exact LinearMap.map_smulₛₗ (h x) c y

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
