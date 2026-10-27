module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtDual
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.CGT.PushingUpLit.CGT6X

private noncomputable def polarDualData
    {K V A : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] [Group A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : A →* MulAut (Multiplicative V))
    (hρ : ∀ (a : A) (v w : V),
      B (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd v)))
        (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd w))) = B v w) :
    PLift (∃ ι : Multiplicative V ≃* Dual (Multiplicative V),
      ∀ (a : A) (v : V),
        ι (ρ a (Multiplicative.ofAdd v)) = dualAct ρ a (ι (Multiplicative.ofAdd v))) := by
  classical
  have htwo : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  let ε : K →+ ZMod 2 :=
    Classical.choose (exists_addMonoidHom_eq_one (A := K) htwo (a := 1) one_ne_zero)
  have hε : ε 1 = 1 :=
    Classical.choose_spec (exists_addMonoidHom_eq_one (A := K) htwo (a := 1) one_ne_zero)
  letI : Algebra (ZMod 2) K := ZMod.algebra (R := K) 2
  letI : Module (ZMod 2) V := Module.restrictScalars (ZMod 2) K V
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  refine PLift.up ?_
  let B2 : LinearMap.BilinForm (ZMod 2) V :=
    LinearMap.mk₂ (ZMod 2) (fun v w => ε (B v w))
      (fun v₁ v₂ w => by
        show ε (B (v₁ + v₂) w) = ε (B v₁ w) + ε (B v₂ w)
        rw [map_add, LinearMap.add_apply, map_add])
      (fun c v w => by
        show ε (B (c • v) w) = c • ε (B v w)
        rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl <;> simp)
      (fun v w₁ w₂ => by
        show ε (B v (w₁ + w₂)) = ε (B v w₁) + ε (B v w₂)
        rw [map_add, map_add])
      (fun c v w => by
        show ε (B v (c • w)) = c • ε (B v w)
        rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl <;> simp)
  have hB2_apply : ∀ v w : V, B2 v w = ε (B v w) := fun v w => rfl
  have hB2 : B2.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro v hv
      by_contra hne
      have hex : ∃ w : V, B v w ≠ 0 := by
        by_contra h
        exact hne (hB.1 v (fun w => by
          by_contra hw
          exact h ⟨w, hw⟩))
      obtain ⟨w, hw⟩ := hex
      have h1 : B v ((B v w)⁻¹ • w) = 1 := by
        rw [map_smul, smul_eq_mul]
        exact inv_mul_cancel₀ hw
      have h2 := hv ((B v w)⁻¹ • w)
      rw [hB2_apply, h1, hε] at h2
      exact one_ne_zero h2
    · intro w hw
      by_contra hne
      have hex : ∃ v : V, B v w ≠ 0 := by
        by_contra h
        exact hne (hB.2 w (fun v => by
          by_contra hv
          exact h ⟨v, hv⟩))
      obtain ⟨v, hv⟩ := hex
      have h1 : B ((B v w)⁻¹ • v) w = 1 := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ hv
      have h2 := hw ((B v w)⁻¹ • v)
      rw [hB2_apply, h1, hε] at h2
      exact one_ne_zero h2
  let iotaFun : V → Dual (Multiplicative V) := fun v =>
    { toFun := fun w => Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd w)))
      map_one' := by
        show Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd 1))) = 1
        simp
      map_mul' := fun w w' => by
        show Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd (w * w')))) =
          Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd w))) *
            Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd w')))
        rw [toAdd_mul, map_add, map_add, ofAdd_add] }
  let iotaHom : Multiplicative V →* Dual (Multiplicative V) :=
    { toFun := fun x => iotaFun (Multiplicative.toAdd x)
      map_one' := by
        show iotaFun (Multiplicative.toAdd 1) = 1
        rw [toAdd_one]
        ext w
        simp [iotaFun]
      map_mul' := fun x y => by
        show iotaFun (Multiplicative.toAdd (x * y)) =
          iotaFun (Multiplicative.toAdd x) * iotaFun (Multiplicative.toAdd y)
        rw [toAdd_mul]
        ext w
        show Multiplicative.ofAdd
            (ε (B (Multiplicative.toAdd x + Multiplicative.toAdd y)
              (Multiplicative.toAdd w))) =
          Multiplicative.ofAdd (ε (B (Multiplicative.toAdd x) (Multiplicative.toAdd w))) *
            Multiplicative.ofAdd (ε (B (Multiplicative.toAdd y) (Multiplicative.toAdd w)))
        rw [map_add, LinearMap.add_apply, map_add, ofAdd_add] }
  have iotaHom_apply : ∀ (x : Multiplicative V) (w : Multiplicative V),
      iotaHom x w =
        Multiplicative.ofAdd (ε (B (Multiplicative.toAdd x) (Multiplicative.toAdd w))) :=
    fun x w => rfl
  have hinj : Function.Injective iotaHom := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx0 : Multiplicative.toAdd x = 0 := by
      apply hB2.1 (Multiplicative.toAdd x)
      intro w
      have h := congrArg (fun f : Dual (Multiplicative V) => f (Multiplicative.ofAdd w)) hx
      simp only [iotaHom_apply, dual_one_apply, toAdd_ofAdd] at h
      have h' := congrArg Multiplicative.toAdd h
      simpa [hB2_apply] using h'
    exact Multiplicative.toAdd.injective (by simpa using hx0)
  have hsurj : Function.Surjective iotaHom := by
    intro φ
    let ℓ : Module.Dual (ZMod 2) V :=
      { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
        map_add' := by
          intro v w
          change Multiplicative.toAdd (φ (Multiplicative.ofAdd (v + w))) =
            Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) +
              Multiplicative.toAdd (φ (Multiplicative.ofAdd w))
          rw [ofAdd_add, map_mul, toAdd_mul]
        map_smul' := by
          intro c v
          rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl <;> simp }
    let v : V := (B2.toDual hB2).symm ℓ
    have hv : B2.toDual hB2 v = ℓ := LinearEquiv.apply_symm_apply _ _
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    ext w
    show Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd w))) = φ w
    have hℓ : ε (B v (Multiplicative.toAdd w)) =
        Multiplicative.toAdd (φ (Multiplicative.ofAdd (Multiplicative.toAdd w))) := by
      have h := congrArg (fun f : Module.Dual (ZMod 2) V => f (Multiplicative.toAdd w)) hv
      rw [LinearMap.BilinForm.toDual_def hB2] at h
      change ε (B v (Multiplicative.toAdd w)) =
        Multiplicative.toAdd (φ (Multiplicative.ofAdd (Multiplicative.toAdd w)))
      rw [← hB2_apply]
      exact h
    rw [hℓ]
    exact congrArg φ (ofAdd_toAdd w)
  let ι : Multiplicative V ≃* Dual (Multiplicative V) :=
    MulEquiv.ofBijective iotaHom ⟨hinj, hsurj⟩
  refine ⟨ι, ?_⟩
  intro a v
  apply MonoidHom.ext
  intro w
  show Multiplicative.ofAdd (ε (B (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd v)))
      (Multiplicative.toAdd w))) =
    Multiplicative.ofAdd (ε (B v (Multiplicative.toAdd (ρ a⁻¹ w))))
  have hfix : Multiplicative.toAdd
      (ρ a⁻¹ (Multiplicative.ofAdd
        (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd v))))) = v := by
    rw [ofAdd_toAdd, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hw : Multiplicative.toAdd
      (ρ a⁻¹ (Multiplicative.ofAdd (Multiplicative.toAdd w))) =
      Multiplicative.toAdd (ρ a⁻¹ w) := by
    rw [ofAdd_toAdd]
  have h := hρ a⁻¹ (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd v)))
    (Multiplicative.toAdd w)
  rw [hfix, hw] at h
  exact congrArg (fun x => Multiplicative.ofAdd (ε x)) h.symm

theorem exists_equivariant_dual_of_invariant_polar
    {K V A : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] [Group A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : A →* MulAut (Multiplicative V))
    (hρ : ∀ (a : A) (v w : V),
      B (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd v)))
        (Multiplicative.toAdd (ρ a (Multiplicative.ofAdd w))) = B v w) :
    ∃ ι : Multiplicative V ≃* Dual (Multiplicative V),
      ∀ (a : A) (v : V),
        ι (ρ a (Multiplicative.ofAdd v)) = dualAct ρ a (ι (Multiplicative.ofAdd v)) :=
  (polarDualData (K := K) (V := V) (A := A) B hB ρ hρ).down

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
