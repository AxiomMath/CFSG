module

public import CFSG.LocalAnalysis.SignalizerFunctor.QuadraticEndomorphisms

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [CommGroup GroupType]

@[expose] def elementaryAutomorphismEnd (prime : ℕ) [Module (ZMod prime) (Additive GroupType)] :
    MulAut GroupType →* Module.End (ZMod prime) (Additive GroupType) where
  toFun automorphism := AddMonoidHom.toZModLinearMap prime automorphism.toAdditive.toAddMonoidHom
  map_one' := by ext element; rfl
  map_mul' first second := by ext element; rfl

theorem elementary_automorphism_end_apply (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] (automorphism : MulAut GroupType)
    (element : Additive GroupType) :
    elementaryAutomorphismEnd prime automorphism element = Additive.ofMul (automorphism element.toMul) := rfl

theorem elementary_automorphism_end_injective (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] :
    Function.Injective (elementaryAutomorphismEnd (GroupType := GroupType) prime) := by
  intro first second equal
  apply MulEquiv.ext
  intro element
  exact congrArg (fun operator => (operator (Additive.ofMul element)).toMul) equal

theorem elementary_automorphism_end_quadratic (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] (automorphism : MulAut GroupType)
    (quadratic : ∀ element : GroupType,
      automorphism (element⁻¹ * automorphism element) = element⁻¹ * automorphism element) :
    (elementaryAutomorphismEnd prime automorphism - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro element
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply]
  rw [elementary_automorphism_end_apply, elementary_automorphism_end_apply]
  simp only [sub_eq_add_neg]
  apply Additive.toMul.injective
  change automorphism (automorphism element.toMul * element.toMul⁻¹) *
    (automorphism element.toMul * element.toMul⁻¹)⁻¹ = 1
  have fixed := quadratic element.toMul
  have difference_eq : automorphism element.toMul * element.toMul⁻¹ =
      element.toMul⁻¹ * automorphism element.toMul := mul_comm _ _
  rw [difference_eq, fixed, mul_inv_cancel]

theorem elementary_automorphism_end_prime_power (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] (automorphism : MulAut GroupType)
    (quadratic : (elementaryAutomorphismEnd prime automorphism - 1) ^ 2 = 0) : automorphism ^ prime = 1 := by
  have power := square_zero_one_add_power (elementaryAutomorphismEnd prime automorphism - 1) quadratic prime
  have one_add : 1 + (elementaryAutomorphismEnd prime automorphism - 1) =
      elementaryAutomorphismEnd prime automorphism := by noncomm_ring
  have cast_zero : (prime : Module.End (ZMod prime) (Additive GroupType)) = 0 := by
    ext element
    simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul (ZMod prime), ZMod.natCast_self, zero_smul,
      LinearMap.zero_apply]
  rw [one_add, cast_zero, zero_mul, add_zero] at power
  apply elementary_automorphism_end_injective prime
  rwa [map_pow, map_one]

end CFSG.SignalizerFunctor.Helpers
