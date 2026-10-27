module

public import CFSG.Quasithin.Background.SzG11TensorA
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

namespace Tensor

open Matrix

@[expose] def zmodEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ZMod 2) M]
    [Module (ZMod 2) N] (e : M ≃+ N) : M ≃ₗ[ZMod 2] N :=
  { e with map_smul' := fun c x => ZMod.map_smul e c x }

@[simp] theorem zmodEquiv_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 2) M] [Module (ZMod 2) N] (e : M ≃+ N) (x : M) : zmodEquiv e x = e x := rfl

section FStructure

variable {K : Type} [Field K] [Algebra (ZMod 2) K]
  {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

abbrev moduleOfAlgHom (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) : Module K I :=
  Module.compHom I κ.toRingHom

theorem moduleOfAlgHom_smul (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) (k : K) (x : I) :
    let _ := moduleOfAlgHom κ
    k • x = κ k x := rfl

theorem isScalarTower_moduleOfAlgHom (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) :
    let _ := moduleOfAlgHom κ
    IsScalarTower (ZMod 2) K I := by
  let _ := moduleOfAlgHom κ
  refine ⟨fun r k x => ?_⟩
  rw [moduleOfAlgHom_smul, moduleOfAlgHom_smul, map_smul]
  rfl

theorem finrank_zmod_two_eq_two [Finite K] (hK : Nat.card K = 4) :
    Module.finrank (ZMod 2) K = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [hK, Nat.card_zmod] at h
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem two_mul_finrank_eq [Finite K] [Finite I] (hK : Nat.card K = 4)
    (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) :
    let _ := moduleOfAlgHom κ
    2 * Module.finrank K I = Module.finrank (ZMod 2) I := by
  let _ := moduleOfAlgHom κ
  have _ := isScalarTower_moduleOfAlgHom κ
  have := Module.finrank_mul_finrank (ZMod 2) K I
  rw [finrank_zmod_two_eq_two hK] at this
  exact this

theorem even_finrank_of_algHom [Finite K] [Finite I] (hK : Nat.card K = 4)
    (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) : Even (Module.finrank (ZMod 2) I) := by
  let _ := moduleOfAlgHom κ
  have h : 2 * Module.finrank K I = Module.finrank (ZMod 2) I := two_mul_finrank_eq hK κ
  exact ⟨Module.finrank K I, by omega⟩

end FStructure

section Natural

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K]
  {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]

theorem natural_module (hK : Nat.card K = 4) (hI : Module.finrank (ZMod 2) I = 4)
    (κ : K →ₐ[ZMod 2] Module.End (ZMod 2) I) {G : Type} [Group G] (hperf : commutator G = ⊤)
    (hcard : Nat.card G = 60) (ρ : G →* (I ≃ₗ[ZMod 2] I)) (hρ : Function.Injective ρ)
    (hcomm : ∀ (k : K) (g : G) (x : I), κ k (ρ g x) = ρ g (κ k x)) :
    ∃ (α : G ≃* SpecialLinearGroup (Fin 2) K) (ι : I ≃ₗ[ZMod 2] (Fin 2 → K)),
      ∀ (g : G) (x : I), ι (ρ g x) =
        ((α g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ι x := by
  classical
  let _ := moduleOfAlgHom κ
  have _ := isScalarTower_moduleOfAlgHom κ
  have hfin : Module.finrank K I = 2 := by
    have h : 2 * Module.finrank K I = Module.finrank (ZMod 2) I := two_mul_finrank_eq hK κ
    omega
  have : Module.Finite K I := Module.Finite.of_finite
  let b : Module.Basis (Fin 2) K I := Module.finBasisOfFinrankEq K I hfin
  let L : G →* Module.End K I :=
    { toFun := fun g =>
        { toFun := fun x => ρ g x
          map_add' := fun x y => map_add (ρ g) x y
          map_smul' := fun k x => by
            rw [RingHom.id_apply, moduleOfAlgHom_smul, moduleOfAlgHom_smul]
            exact (hcomm k g x).symm }
      map_one' := LinearMap.ext fun x => by
        show ρ 1 x = x
        rw [map_one]
        rfl
      map_mul' := fun g g' => LinearMap.ext fun x => by
        show ρ (g * g') x = ρ g (ρ g' x)
        rw [map_mul]
        rfl }
  let f : G →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => LinearMap.toMatrix b b (L g)
      map_one' := by
        rw [map_one]
        exact LinearMap.toMatrix_one b
      map_mul' := fun g g' => by
        rw [map_mul]
        exact LinearMap.toMatrix_mul b _ _ }
  have hf : Function.Injective f := by
    intro g g' h
    have h1 : L g = L g' := (LinearMap.toMatrix b b).injective h
    apply hρ
    refine LinearEquiv.ext fun x => ?_
    exact congrArg (fun T : Module.End K I => T x) h1
  obtain ⟨α, hα⟩ := exists_mulEquiv_specialLinear hK hperf hcard f hf
  refine ⟨α, zmodEquiv b.equivFun.toAddEquiv, fun g x => ?_⟩
  rw [hα g]
  show b.equivFun (ρ g x) = LinearMap.toMatrix b b (L g) *ᵥ b.equivFun x
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b (L g) x).symm

end Natural

end Tensor

end SzG11S

end G11

end CFSG.Quasithin
